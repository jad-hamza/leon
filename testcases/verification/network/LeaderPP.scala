package distribution

import leon.collection._

import Protocol._
import ProtocolProof._
import Networking._
import FifoNetwork._

object PrettyPrinting {
  
  def stateToString(s: State) = {
    s match {
      case Participant() => "Participant"
      case NonParticipant() => "NonParticipant"
      case KnowLeader(i) => "KnowLeader(" + i + ")"
    }
  }
  
  def actorIdToString(id: ActorId) = {
    id match {
      case UID(uid) => "u" + uid
    }
  }
  
  def statesToString(m: MMap[ActorId,State]): String = {
    require(mapDefined(n, m))
  
    def loop(i: BigInt) : String = {
      if (i == n) ""
      else  
        actorIdToString(UID(i)) + " -> " + stateToString(m(UID(i))) + "\n" + loop(i+1)
    }
    
    loop(0)
  }
  
  def messageToString(m: Message) = {
    m match  {
      case Election(i) => "Election(" + i + ")"
      case Elected(i) => "Elected(" + i + ")"
    }
  }
  
  def messageListToString(ms: List[Message]): String = {
    ms match {
      case Nil() => "[]"
      case Cons(x, xs) =>  messageToString(x) + ", " + messageListToString(xs)
    }
  }
  
  
  def messagesToString(m: MMap[(ActorId,ActorId), List[Message]]): String = {
  
    def loop(i: BigInt) : String = {
      if (i == n) ""
      else  
        actorIdToString(UID(i)) + "," + actorIdToString(UID((i+1)%n)) + ": " + messageListToString(m.getOrElse((UID(i),UID((i+1)%n)), Nil())) + "\n" + loop(i+1)
    }
    
    loop(0)
  }
  
  def actorToString(a: Actor) = {
    a match {
      case Process(id) => "Process(" + actorIdToString(id) + ")"
    }
  }
  
  def getActorToString(getActor: MMap[ActorId,Actor]) = {
    
    def loop(i: BigInt) : String = {
      if (i == n) ""
      else  
        "getActor(" + i + ") = " + actorToString(getActor(UID(i))) + "\n" + loop(i+1)
    }
  
    loop(0)
  }
  
  def networkToString(n: VerifiedNetwork): String = {
    val VerifiedNetwork(states, messages, getActor) = n
    
    "\n\n" + statesToString(states) + "\n\n" + 
    messagesToString(messages) + "\n\n" + 
    getActorToString(getActor) + "\n"
  }
  
}