use std::env;
use std::time::Duration;

use libot::{Bot, run};
use libot::client::{BotClient, BotClientBuilder};
use libot::model::{
    ChallengeDeclinedEvent,
    ChallengeEvent,
    Color,
    DeclineReason,
    GameContext,
    GameStartFinishEvent,
    GameStateEvent,
    Milliseconds
};

use kvarko_engine::{KvarkoEngine, StateEvaluatingController, StateEvaluator};
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

struct KvarkoBot;

#[async_trait::async_trait]
impl Bot for KvarkoBot {

    async fn on_game_start(&self, game: GameStartFinishEvent, _: &BotClient) {
        println!("Game Start: {:?}", game);
    }

    async fn on_game_finish(&self, game: GameStartFinishEvent, _: &BotClient) {
        println!("Game Finish: {:?}", game);
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
            let bot_color = game_context.bot_color;
            let turn = kvarko_state.position().turn();

            if bot_color != Some(map_player(turn)) {
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

            client.make_move(game_context.id.clone(), move_uci, false).await.unwrap();
        }
    }
}

#[tokio::main]
async fn main() {
    let token = env::args().nth(1).expect("provide an API token as a CLI argument");
    let client = BotClientBuilder::new()
        .with_token(token)
        .build().unwrap();

    match run(KvarkoBot, client).await {
        Ok(_) => { },
        Err(e) => {
            eprintln!("error running bot: {}", e)
        }
    }
}
