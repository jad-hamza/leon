package distribution

import leon.collection._

import Protocol._
import ProtocolProof._
import Networking._
import FifoNetwork._

object PrettyPrinting {
  
  val a1 = ActorId1()
  val a2 = ActorId2()
  
  def stateToString(s: State) = {
    s match {
      case CCounter(i) => "CCounter(" + i + ")"
      case VCounter(i) => "VCounter(" + i + ")"
      case BadState() => "BadState"
    }
  }
  
  def actorIdToString(id: ActorId) = {
    id match {
      case ActorId1() => "A1"
      case ActorId2() => "A2"
    }
  }
  
  def statesToString(m: MMap[ActorId,State]): String = {
    require(m.contains(a1) && m.contains(a2))
    
    actorIdToString(a1) + " -> " + stateToString(m(a1)) + "\n" +
    actorIdToString(a2) + " -> " + stateToString(m(a2)) + "\n"
  }
  
  def messageToString(m: Message) = {
    m match  {
      case Deliver(j) => "Deliver(" + j + ")"
      case Increment() => "Increment"
    }
  }
  
  def messageListToString(ms: List[Message]): String = {
    ms match {
      case Nil() => "[]"
      case Cons(x, xs) =>  messageToString(x) + ", " + messageListToString(xs)
    }
  }
  
  
  def messagesToString(m: MMap[(ActorId,ActorId), List[Message]]): String = {
    actorIdToString(a1) + "," + actorIdToString(a1) + ": " + messageListToString(m.getOrElse((a1,a1), Nil())) + "\n" +
    actorIdToString(a1) + "," + actorIdToString(a2) + ": " + messageListToString(m.getOrElse((a1,a2), Nil())) + "\n"
  }
  
  def actorToString(a: Actor) = {
    a match {
      case CountingActor(id) => "CountingActor(" + actorIdToString(id) + ")"
      case CheckingActor(id) => "CheckingActor(" + actorIdToString(id) + ")"
    }
  }
  
  def networkToString(n: VerifiedNetwork): String = {
    require(networkInvariant(n.param, n.states, n.messages, n.getActor))
    val VerifiedNetwork(_, states, messages, getActor) = n
    
    "\n\n" + statesToString(states) + "\n\n" + 
    messagesToString(messages) + "\n\n" + 
    "getActor(1) = " + actorToString(getActor(actor1)) + "\n" +
    "getActor(2) = " + actorToString(getActor(actor2)) + "\n\n"
  }
  
}