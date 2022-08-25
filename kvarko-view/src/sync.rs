use tokio::sync::mpsc::{self, Receiver as MpscReceiver, Sender as MpscSender};
use tokio::sync::mpsc::error::SendError as MpscSendError;
use tokio::sync::oneshot::{self, Sender as OneshotSender};
use tokio::sync::oneshot::error::RecvError as OneshotRecvError;

#[derive(Debug)]
pub enum QueryError<Q, R> {
    SendError(MpscSendError<(Q, OneshotSender<R>)>),
    RecvError(OneshotRecvError)
}

impl<Q, R> From<MpscSendError<(Q, OneshotSender<R>)>> for QueryError<Q, R> {
    fn from(e: MpscSendError<(Q, OneshotSender<R>)>) -> QueryError<Q, R> {
        QueryError::SendError(e)
    }
}

impl<Q, R> From<OneshotRecvError> for QueryError<Q, R> {
    fn from(e: OneshotRecvError) -> QueryError<Q, R> {
        QueryError::RecvError(e)
    }
}

#[derive(Clone)]
pub struct Requester<Q, R> {
    sender: MpscSender<(Q, OneshotSender<R>)>
}

impl<Q, R> Requester<Q, R> {

    pub fn query(&mut self, query: Q) -> Result<R, QueryError<Q, R>> {
        let (sender, receiver) = oneshot::channel();
        self.sender.blocking_send((query, sender))?;
        Ok(receiver.blocking_recv()?)
    }
}

pub struct ResponseHandle<R> {
    sender: Option<OneshotSender<R>>
}

impl<R> ResponseHandle<R> {

    pub fn send_response(mut self, response: R) -> Result<(), R> {
        self.sender.take().unwrap().send(response)
    }
}

impl<R> Drop for ResponseHandle<R> {
    fn drop(&mut self) {
        if self.sender.is_some() {
            panic!("ResponseHandle dropped without sending response")
        }
    }
}

pub struct Responder<Q, R> {
    receiver: MpscReceiver<(Q, OneshotSender<R>)>
}

impl<Q, R> Responder<Q, R> {

    pub fn recv(&mut self) -> Option<(Q, ResponseHandle<R>)> {
        self.receiver.try_recv()
            .ok()
            .map(|(q, sender)| (q, ResponseHandle {
                sender: Some(sender)
            }))
    }
}

pub fn channel<Q, R>() -> (Requester<Q, R>, Responder<Q, R>) {
    let (sender, receiver) = mpsc::channel(1);
    let requester = Requester { sender };
    let responder = Responder { receiver };
    (requester, responder)
}
