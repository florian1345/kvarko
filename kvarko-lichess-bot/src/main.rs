use std::env;
use libot::{Bot, BotClientBuilder, run};
use libot::model::{Challenge, ChallengeDeclined, GameEventInfo};

struct LoggingBot;

#[async_trait::async_trait]
impl Bot for LoggingBot {

    async fn on_game_start(&self, game: GameEventInfo) {
        println!("Game Start: {:?}", game);
    }

    async fn on_game_finish(&self, game: GameEventInfo) {
        println!("Game Finish: {:?}", game);
    }

    async fn on_challenge(&self, challenge: Challenge) {
        println!("Challenge: {:?}", challenge);
    }

    async fn on_challenge_cancelled(&self, challenge: Challenge) {
        println!("Challenge Canceled: {:?}", challenge);
    }

    async fn on_challenge_declined(&self, challenge: ChallengeDeclined) {
        println!("Challenge Declined: {:?}", challenge);
    }
}

#[tokio::main]
async fn main() {
    let token = env::args().skip(1).next().expect("provide an API token as a CLI argument");
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
