use std::env;
use libot::{Bot, BotClient, BotClientBuilder, run};
use libot::model::{Challenge, ChallengeDeclined, DeclineReason, GameEventInfo};

struct LoggingBot;

#[async_trait::async_trait]
impl Bot for LoggingBot {

    async fn on_game_start(&self, game: GameEventInfo, _: &BotClient) {
        println!("Game Start: {:?}", game);
    }

    async fn on_game_finish(&self, game: GameEventInfo, _: &BotClient) {
        println!("Game Finish: {:?}", game);
    }

    async fn on_challenge(&self, challenge: Challenge, client: &BotClient) {
        if challenge.rated {
            client.decline_challenge(challenge.id, Some(DeclineReason::Casual)).await.unwrap();
        }
        else {
            client.accept_challenge(challenge.id).await.unwrap();
        }
    }

    async fn on_challenge_cancelled(&self, challenge: Challenge, _: &BotClient) {
        println!("Challenge Canceled: {:?}", challenge);
    }

    async fn on_challenge_declined(&self, challenge: ChallengeDeclined, _: &BotClient) {
        println!("Challenge Declined: {:?}", challenge);
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
