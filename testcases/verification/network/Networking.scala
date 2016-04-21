package distribution

import Protocol._
import ProtocolProof._
import FifoNetwork._

import leon.collection._
import leon.proof.check

object Networking {
  
  abstract class ActorId
  abstract class Message
  abstract class State
  
  
  def makeNetwork(states: MMap[ActorId,State], getActor: MMap[ActorId,Actor]) = {
    require(networkInvariant(states, MMap(), getActor))
    
    VerifiedNetwork(states, MMap(), getActor)
  }
  
  abstract class Actor {
    val myId: ActorId
    
    def !!(receiver: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.states, net.messages.updated((myId,receiver), net.messages.getOrElse((myId,receiver),Nil()) :+ m), net.getActor))
      net send (myId,receiver,m)
    } 
    
    def init()(implicit net: VerifiedNetwork): Unit
    def receive(id: ActorId, m: Message)(implicit net: VerifiedNetwork): Unit
    
    def state(implicit net: VerifiedNetwork) = {
      require(net.states.contains(myId))
      net.getState(myId)
    }
    
    def update(s: State)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.states.updated(myId,s), net.messages, net.getActor))
      net.updateState(myId, s)
    }
    
    
  }
  
  
  def runActors(actorIds: List[ActorId], net: VerifiedNetwork, schedule: List[(ActorId,ActorId,Message)]): Unit = {

    def loop(net: VerifiedNetwork, schedule: List[(ActorId,ActorId,Message)]): Unit = {

      schedule match {
        case Nil() => ()
        case Cons((sender, receiver, m), schedule2) =>
          
          if (net.applyMessage(sender, receiver, m)) 
            loop(net, schedule)
            
      }
    } ensuring(_ => networkInvariant(net.states, net.messages, net.getActor))
    
    
    def initializationLoop(net: VerifiedNetwork, initSchedule: List[ActorId]): Unit = {
      initSchedule match {
        case Nil() => ()
        case Cons(x,xs) => 
          net.getActor(x).init()(net)
          initializationLoop(net, xs)
      }
    } ensuring(_ => networkInvariant(net.states, net.messages, net.getActor)) 
  
    initializationLoop(net, actorIds)
    loop(net, schedule)
  
  } ensuring(_ => networkInvariant(net.states, net.messages, net.getActor))

  
}
