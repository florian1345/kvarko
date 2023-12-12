use std::env;
use std::time::Duration;

use libot::{Bot, run};
use libot::client::{BotClient, BotClientBuilder};
use libot::model::{
    ChallengeDeclinedEvent,
    ChallengeEvent,
    ChatLineEvent,
    DeclineReason,
    GameFullEvent,
    GameId,
    GameStartFinishEvent,
    GameStateEvent,
    OpponentGoneEvent
};
use kvarko_engine::depth::IterativeDeepeningForDuration;

use kvarko_engine::{KvarkoEngine, StateEvaluatingController, StateEvaluator};

use kvarko_model::hash::ZobristHasher;
use kvarko_model::state::State;

const DEEPEN_FOR: Duration = Duration::from_secs(1);

type Kvarko = StateEvaluatingController<
    KvarkoEngine<ZobristHasher<u64>, IterativeDeepeningForDuration>>;

fn kvarko_engine() -> Kvarko {
    kvarko_engine::kvarko_engine(DEEPEN_FOR, None)
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

    async fn on_game_full(&self, _: GameId, game_full: GameFullEvent, _: &BotClient) {
        println!("Game Full: {:?}", game_full);
    }

    async fn on_game_state(&self, game_id: GameId, state: GameStateEvent, client: &BotClient) {
        if let Some(mut state) = State::from_uci_history(state.moves.split(' ')) {
            let mut kvarko = kvarko_engine();
            let output = kvarko.evaluate_state(&mut state);
            let move_uci = output.recommended_move.to_uci_notation(state.position()).unwrap();

            client.make_move(game_id, move_uci, false).await.unwrap();
        }
    }

    async fn on_chat_line(&self, _: GameId, chat_line: ChatLineEvent, _: &BotClient) {
        println!("Chat Line: {:?}", chat_line);
    }

    async fn on_opponent_gone(&self, _: GameId, opponent_gone: OpponentGoneEvent, _: &BotClient) {
        println!("Chat Line: {:?}", opponent_gone);
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
