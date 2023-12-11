use std::env;
use libot::{Bot, run};
use libot::client::{BotClient, BotClientBuilder};
use libot::model::{ChallengeDeclinedEvent, ChallengeEvent, ChatLineEvent, DeclineReason, GameFullEvent, GameStartFinishEvent, GameStateEvent, OpponentGoneEvent};

struct LoggingBot;

#[async_trait::async_trait]
impl Bot for LoggingBot {

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

    async fn on_game_full(&self, game_full: GameFullEvent, _client: &BotClient) {
        println!("Game Full: {:?}", game_full);
    }

    async fn on_game_state(&self, state: GameStateEvent, _client: &BotClient) {
        println!("Game State: {:?}", state);
    }

    async fn on_chat_line(&self, chat_line: ChatLineEvent, _client: &BotClient) {
        println!("Chat Line: {:?}", chat_line);
    }

    async fn on_opponent_gone(&self, opponent_gone: OpponentGoneEvent, _client: &BotClient) {
        println!("Chat Line: {:?}", opponent_gone);
    }
}

#[tokio::main]
async fn main() {
    let token = env::args().nth(1).expect("provide an API token as a CLI argument");
    let client = BotClientBuilder::new()
        .with_token(token)
        .build().unwrap();

    match run(LoggingBot, client).await {
        Ok(_) => { },
        Err(e) => {
            eprintln!("error running bot: {}", e)
        }
    }
}
