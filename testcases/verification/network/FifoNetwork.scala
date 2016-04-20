package distribution
 
import leon.collection._
import leon.annotation._
import leon.proof.check

import Protocol._
import ProtocolProof._
import Networking._

object FifoNetwork  {
  
  case class VerifiedNetwork(
      var states: MMap[ActorId,State], 
      var messages: MMap[(ActorId,ActorId),List[Message]], 
      getActor: ActorId => Actor)  {
    require(networkInvariant(states,messages,getActor))
        
    def send(sender: ActorId, receiver: ActorId, m: Message): Unit = {
      require(networkInvariant(states, messages.updated((sender,receiver), messages.getOrElse((sender,receiver),Nil()) :+ m),getActor))
      
      messages = messages.updated((sender,receiver), messages.getOrElse((sender,receiver),Nil()) :+ m)
    } 
    
    def updateState(actor: ActorId, state: State): Unit = {
      require(networkInvariant(states.updated(actor,state),messages,getActor))
      
      states = states.updated(actor,state)
    } 
    
    def getState(actor: ActorId) = {
      require(states.contains(actor))
      states(actor)
    }
    
    
    def applyMessage(sender: ActorId, receiver: ActorId, m: Message): Boolean = {
      require(peekMessageEnsuresReceivePre(this, sender, receiver, m))
      
      val sms = messages.getOrElse((sender,receiver), Nil())
      
    
      sms match {
        case Cons(x, xs) if (x == m) => 
          val messages2 = messages.updated((sender,receiver), xs)
          messages = messages2
          getActor(receiver).receive(sender,m)(this)
          true
          
        case _ => 
          false
      }
      
    } ensuring(_ => networkInvariant(states, messages, getActor))
  }
  
}
