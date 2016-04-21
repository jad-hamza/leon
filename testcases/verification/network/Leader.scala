package distribution


import FifoNetwork._
import Networking._

import leon.lang.BooleanDecorations
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps

// following https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm

object Protocol {
  import ProtocolProof._
  
  val n: BigInt = 3
  val starterProcess: BigInt = 0
  
  case class Election(i: BigInt) extends Message
  case class Elected(i: BigInt) extends Message

  case class NonParticipant() extends State
  case class Participant() extends State
  case class KnowLeader(i: BigInt) extends State
  
  case class UID(uid: BigInt) extends ActorId
    
  case class Process(myId: ActorId) extends Actor {
  
    val UID(myuid) = myId
    val nextProcess = UID((myuid+1)%n)
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
    
      if (myuid == starterProcess)
        !! (nextProcess, Election(myuid))
    }
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
    
      (sender, m, state) match {
        case (id, Election(uid), NonParticipant()) =>
          if (uid > myuid) {
            update (Participant())
            !! (nextProcess, Election(uid))
          } else if (uid < myuid) {
            update (Participant())
            !! (nextProcess, Election(myuid))
          }
          else {
            // I cannot receive an Election message equal to my uid if I'm not a participant
            assert(false)
          }
          
        case (id, Election(uid), Participant()) =>
          if (uid > myuid) {
            !! (nextProcess, Election(uid))
          } else if (uid == myuid) {
            update (KnowLeader(uid))
            !! (nextProcess, Elected(myuid))
            // I'm the leader!!
          } else {
            // discard smaller uid Election message
          }
          
        case (id, Elected(uid), NonParticipant()) =>
          assert(uid == myuid)
          
        case (id, Elected(uid), Participant()) => {
          update (KnowLeader(uid))
          !! (nextProcess, Elected(uid))
        }
              
      }
    } ensuring(_ => networkInvariant(net.states, net.messages, net.getActor))
    
  }
  
}


// This object contains lemma and auxialiary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  
  def mapDefined[T](n: BigInt, m: MMap[ActorId, T]): Boolean = {
    if (n == 0) true
    else m.contains(UID(n-1)) && mapDefined(n-1,m)
  }
  
  def checkProperty(n: BigInt, p: BigInt => Boolean): Boolean = {
    if (n == 0) true
    else p(n-1) && checkProperty(n-1,p)
  }
  
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    checkProperty(n, (i: BigInt) => states.contains(UID(i))) &&
    checkProperty(n, (i: BigInt) => getActor.contains(UID(i)) && getActor(UID(i)).myId == UID(i)) &&
    checkProperty(n, (i: BigInt) => 
      checkProperty(n, (j: BigInt) => 
        j != (i+1)%n ==> !messages.contains(UID(i),UID(j))
      )
    )
  }
  
  def peekMessageEnsuresReceivePre(n: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    true
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    a match {
      case Process(UID(uid)) => true
    }
  }
  
  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def range(n: BigInt): List[BigInt] = {
    require (n >= 0)
    if (n == 0) List()
    else Cons(n-1, range(n-1))
  }

}