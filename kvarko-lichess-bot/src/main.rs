use std::collections::HashSet;
use std::env;
use std::str::FromStr;
use std::sync::RwLock;
use std::time::Duration;

use libot::{Bot, run};
use libot::client::{BotClient, BotClientBuilder};
use libot::error::LibotResult;
use libot::model::{Milliseconds, Seconds};
use libot::model::bot_event::{ChallengeDeclinedEvent, ChallengeEvent, GameStartFinishEvent};
use libot::model::challenge::DeclineReason;
use libot::model::game::{Color, GameContext, GameId};
use libot::model::game::event::{ChatLineEvent, ChatRoom, GameStateEvent};

use kvarko_engine::{KvarkoEngine, KvarkoEngineMetadata, StateEvaluatingController, StateEvaluator, StateEvaluatorOutput};
use kvarko_engine::depth::IterativeDeepeningForDuration;
use kvarko_model::hash::ZobristHasher;
use kvarko_model::player::Player;
use kvarko_model::state::State;

type Kvarko = StateEvaluatingController<
    KvarkoEngine<ZobristHasher<u64>, IterativeDeepeningForDuration>>;

fn kvarko_engine(deepen_for: Duration) -> Kvarko {
    kvarko_engine::kvarko_engine(deepen_for, None)
}

const MIN_FROM_TOTAL: f64 = 0.005;
const MAX_FROM_TOTAL: f64 = 0.05;
const FROM_INCREMENT: f64 = 0.5;
const MILLIS_TO_SECS: f64 = 0.001;

fn compute_deepen_for(total: Milliseconds, increment: Milliseconds) -> Duration {
    let min_from_total = total as f64 * MIN_FROM_TOTAL;
    let max_from_total = total as f64 * MAX_FROM_TOTAL;
    let from_increment = increment as f64 * FROM_INCREMENT;

    let millis = from_increment.min(max_from_total).max(min_from_total);

    Duration::from_secs_f64(millis * MILLIS_TO_SECS)
}

fn map_player(player: Player) -> Color {
    match player {
        Player::White => Color::White,
        Player::Black => Color::Black
    }
}

struct KvarkoBot {
    info_games: RwLock<HashSet<GameId>>
}

const MAX_TIME_PER_REQUEST: Seconds = 60;

const MAX_GIVEN_TIME: Seconds = 1800;

impl KvarkoBot {
    async fn execute_time_command(&self, args: &[&str], context: &GameContext, client: &BotClient)
            -> LibotResult<()> {
        if args.len() != 1 {
            client.send_chat_message(context.id.clone(), ChatRoom::Player,
                "Expect exactly 1 argument (number of seconds).").await?;
            return Ok(());
        }

        if let Ok(mut seconds) = Seconds::from_str(args[0]) {
            if seconds > 0 && seconds <= MAX_GIVEN_TIME {
                while seconds > MAX_TIME_PER_REQUEST {
                    client.add_time(context.id.clone(), MAX_TIME_PER_REQUEST).await?;
                    seconds -= MAX_TIME_PER_REQUEST;
                }

                client.add_time(context.id.clone(), seconds).await?;
                client.send_chat_message(context.id.clone(), ChatRoom::Player, "Ok.").await?;
            }
            else {
                client.send_chat_message(context.id.clone(), ChatRoom::Player,
                    "Number of seconds must be between 1 and 86400.").await?;
            }
        }
        else {
            client.send_chat_message(context.id.clone(), ChatRoom::Player,
                "Not a valid number.").await?;
        }

        Ok(())
    }

    async fn execute_info_command(&self, args: &[&str], context: &GameContext, client: &BotClient)
            -> LibotResult<()> {
        if !args.is_empty() {
            client.send_chat_message(context.id.clone(), ChatRoom::Player,
                "No arguments expected.").await?;
            return Ok(());
        }

        self.info_games.write().unwrap().insert(context.id.clone());
        client.send_chat_message(context.id.clone(), ChatRoom::Player, "Ok.").await?;

        Ok(())
    }

    async fn send_info(&self, output: StateEvaluatorOutput<KvarkoEngineMetadata>,
            game_id: GameId, client: &BotClient) -> LibotResult<()> {
        if !self.info_games.read().unwrap().contains(&game_id) {
            return Ok(());
        }

        let message = match output.metadata {
            KvarkoEngineMetadata::BookMove =>
                format!("Book Move\nEval: {:.2} pawns", output.evaluation),
            KvarkoEngineMetadata::ComputedMove(tree_search_metadata) =>
                format!("Computed Move\nEval: {:.2} pawns\nDepth: {} ply",
                    output.evaluation, tree_search_metadata.depth)
        };
        client.send_chat_message(game_id, ChatRoom::Player, message).await.unwrap();

        Ok(())
    }
}

#[async_trait::async_trait]
impl Bot for KvarkoBot {

    async fn on_game_start(&self, game: GameStartFinishEvent, _: &BotClient) {
        println!("Game Start: {:?}", game);
    }

    async fn on_game_finish(&self, game: GameStartFinishEvent, _: &BotClient) {
        if let Some(game_id) = game.id {
            if self.info_games.read().unwrap().contains(&game_id) {
                self.info_games.write().unwrap().remove(&game_id);
            }
        }
    }

    async fn on_challenge(&self, challenge: ChallengeEvent, client: &BotClient) {
        if challenge.rated {
            client.decline_challenge(challenge.id, Some(DeclineReason::Casual)).await.unwrap();
        }
        else {
            client.accept_challenge(challenge.id).await.unwrap();
        }
    }

    async fn on_challenge_cancelled(&self, challenge: ChallengeEvent, _: &BotClient) {
        println!("Challenge Canceled: {:?}", challenge);
    }

    async fn on_challenge_declined(&self, challenge: ChallengeDeclinedEvent, _: &BotClient) {
        println!("Challenge Declined: {:?}", challenge);
    }

    async fn on_game_state(&self, game_context: &GameContext, state: GameStateEvent,
            client: &BotClient) {
        let kvarko_state = if state.moves.is_empty() {
            Some(State::initial())
        }
        else {
            State::from_uci_history(state.moves.split(' '))
        };

        if let Some(mut kvarko_state) = kvarko_state {
            let turn = kvarko_state.position().turn();

            if game_context.bot_color != Some(map_player(turn)) || !state.status.is_running() {
                return;
            }

            let (total, increment) = match turn {
                Player::White => (state.white_time, state.white_increment),
                Player::Black => (state.black_time, state.black_increment)
            };
            let deepen_for = compute_deepen_for(total, increment);

            let mut kvarko = kvarko_engine(deepen_for);
            let output = kvarko.evaluate_state(&mut kvarko_state);
            let move_uci =
                output.recommended_move.to_uci_notation(kvarko_state.position()).unwrap();

            if let Err(e) = client.make_move(game_context.id.clone(), move_uci, false).await {
                eprintln!("error sending move: {:?}", e); // TODO proper tracing
            }

            self.send_info(output, game_context.id.clone(), client).await.unwrap();
        }
    }

    async fn on_chat_line(&self, context: &GameContext, chat_line: ChatLineEvent,
            client: &BotClient) {
        if context.bot_color.is_some() && chat_line.text.starts_with('!') {
            let parts = chat_line.text[1..].split(' ').collect::<Vec<_>>();
            let (&command, args) = parts.split_first().unwrap();

            match command {
                // TODO error handling
                "time" => self.execute_time_command(args, context, client).await.unwrap(),
                "info" => self.execute_info_command(args, context, client).await.unwrap(),
                _ => {}
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let token = env::args().nth(1).expect("provide an API token as a CLI argument");
    let client = BotClientBuilder::new()
        .with_token(token)
        .build().unwrap();
    let bot = KvarkoBot {
        info_games: RwLock::new(HashSet::new())
    };

    match run(bot, client).await {
        Ok(_) => { },
        Err(e) => {
            eprintln!("error running bot: {}", e)
        }
    }
}
