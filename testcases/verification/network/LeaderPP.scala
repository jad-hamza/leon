package distribution

import leon.collection._
import leon.proof._


import Protocol._
import ProtocolProof._
import Networking._
import FifoNetwork._
import Quantifiers._


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

  def statesToString(n: BigInt, m: MMap[ActorId,State]): String = {

    def loop(i: BigInt) : String = {
      if (i == n) ""
      else  if (m.contains(UID(i)))
        actorIdToString(UID(i)) + " -> " + stateToString(m(UID(i))) + "\n" + loop(i+1)
      else
        actorIdToString(UID(i)) + " -> Nothing\n" + loop(i+1)
    }

    "\n"+loop(0)
  }

  def noParamStatesToString(m: MMap[ActorId,State]): String = statesToString(5, m)
  
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
  
  
  def messagesToString(n: BigInt, m: MMap[(ActorId,ActorId), List[Message]]): String = {
  
    def loop(i: BigInt) : String = {
      require(0 <= i && i <= n)
      if (i == n) ""
      else  
        actorIdToString(UID(i)) + "," + actorIdToString(UID(increment(i,n))) + ": " + messageListToString(m.getOrElse((UID(i),UID(increment(i,n))), Nil())) + "\n" + loop(i+1)
    }
    
    if (n >= 0)
      "\n"+loop(0)
    else ""
  }

  def noParamMessagesToString(m: MMap[(ActorId,ActorId), List[Message]]): String = {
    messagesToString(5, m)
  }
  
  def actorToString(a: Actor) = {
    a match {
      case Process(id, ssn) => "Process(" + actorIdToString(id) + ", " + ssn + ")"
    }
  }

  def getActorToString(n: BigInt, getActor: MMap[ActorId,Actor]) = {

    def loop(i: BigInt) : String = {
      require(0 <= i && i <= n)
      if (i == n) ""
      else if (getActor.contains(UID(i))) {
        "getActor(" + i + ") = " + actorToString(getActor(UID(i))) + "\n" + loop(i+1)
      } else {
        "getActor(" + i + ") = Nothing\n" + loop(i+1)
      }
    }

    if (n >= 0)
      "\n"+loop(0)
    else ""
  }

  def noParamGetActorToString(getActor: MMap[ActorId,Actor]) = {

    getActorToString(5,getActor)
  }

  def ssnsToString(n: BigInt, ssns: BigInt => BigInt): String = {
    def loop(i: BigInt): String = {
      require(0 <= i && i <= n)
      if (i == n) ""
      else "ssns(" + i + ") = " + ssns(i) + "\n" + loop(i+1)
    }
    if (n >= 0) "\n"+loop(0)
    else ""
  }
  
  def networkToString(net: VerifiedNetwork): String = {
    val VerifiedNetwork(p, states, messages, getActor) = net
    val Params(n, starterProcess, ssns) = p


    "\n\nNumber of processes: " + n.toString + "\n" +
    "Starting Process: " + starterProcess + "\n\n" +
    ssnsToString(n, ssns) + "\n\n" +
    statesToString(n, states) + "\n\n" + 
    messagesToString(n, messages) + "\n\n" + 
    getActorToString(n, getActor) + "\n"
  }
  
}