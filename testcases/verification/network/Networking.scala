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
  abstract class Parameter
  
  
  abstract class Actor {
    val myId: ActorId
    
    def !!(receiver: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      net send (myId,receiver,m)
    } 
    
    def init()(implicit net: VerifiedNetwork): Unit
    def receive(id: ActorId, m: Message)(implicit net: VerifiedNetwork): Unit
    
    def state(implicit net: VerifiedNetwork) = {
      require(net.states.contains(myId))
      net.getState(myId)
    }
    
    def update(s: State)(implicit net: VerifiedNetwork) = {
      net.updateState(myId, s)
    }
    
    
  }
  
  
  def runActors(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]): Unit = {
    require(runActorsPrecondition(p, initial_actor, schedule))
  
    val net = makeNetwork(p)
    
  
    def loop(schedule: List[(ActorId,ActorId,Message)]): Unit = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))

      schedule match {
        case Nil() => ()
        case Cons((sender, receiver, m), schedule2) =>
          
          if (validId(net, sender) && validId(net, receiver) && net.applyMessage(sender, receiver, m))
            loop(schedule2)
            
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  
    initial_actor.init()(net)
    loop(schedule)
  
  } 

  
}
