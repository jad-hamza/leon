package distribution
 
import leon.collection._
import leon.annotation._
import leon.proof.check

import Protocol._
import ProtocolProof._
import Networking._

object FifoNetwork  {
  
  case class VerifiedNetwork(
      param: Parameter,
      var states: MMap[ActorId,State], 
      var messages: MMap[(ActorId,ActorId),List[Message]], 
      getActor: MMap[ActorId,Actor])  {
        
    def send(sender: ActorId, receiver: ActorId, m: Message): Unit = {
      messages = messages.updated((sender,receiver), messages.getOrElse((sender,receiver),Nil()) :+ m)
    } 
    
    def updateState(actor: ActorId, state: State): Unit = {
      states = states.updated(actor,state)
    } 
    
    def getState(actor: ActorId) = {
      require(states.contains(actor))
      states(actor)
    }
    
    
    def applyMessage(sender: ActorId, receiver: ActorId, m: Message): Boolean = {
      require(
        networkInvariant(param, states, messages, getActor) &&
        validId(this, sender) && 
        validId(this, receiver) &&
        peekMessageEnsuresReceivePre(this, sender, receiver, m)
      )
      
      val sms = messages.getOrElse((sender,receiver), Nil())
      
    
      sms match {
        case Cons(x, xs) if (x == m) => 
          val messages2 = messages.updated((sender,receiver), xs)
          messages = messages2
          check(networkInvariant(param, states, messages, getActor))
          getActor(receiver).receive(sender,m)(this)
          check(networkInvariant(param, states, messages, getActor))
          true

        case _ => 
          false
      }
      
    } ensuring(networkInvariant(param, states, messages, getActor))
  }
  
}
