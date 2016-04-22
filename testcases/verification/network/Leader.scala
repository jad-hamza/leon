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
  
  val starterProcess: BigInt = 0
  
  case class Election(i: BigInt) extends Message
  case class Elected(i: BigInt) extends Message

  case class NonParticipant() extends State
  case class Participant() extends State
  case class KnowLeader(i: BigInt) extends State
  
  case class UID(uid: BigInt) extends ActorId
  
  case class Size(n: BigInt) extends Parameter
  
  
  def increment(i: BigInt, n: BigInt): BigInt = {
    if (i < n-1) i+1
    else 0
  }
    
  case class Process(myId: ActorId) extends Actor {
  
    val UID(myuid) = myId
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
      val Size(n) = net.param
      val nextProcess = UID(increment(myuid, n))
    
      if (myuid == starterProcess)
        !! (nextProcess, Election(myuid))
    }
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
//       require(receivePre(this, sender, m))
      
      val Size(n) = net.param
      val nextProcess = UID(increment(myuid, n))
    
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
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  }
  
}


// This object contains lemma and auxialiary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  

  def checkProperty(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0)
    
    if (n == 0) true
    else p(n-1) && checkProperty(n-1,p)
  }
  
  
  def decrease(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0 && checkProperty(n, p))
    
    n == 0 || checkProperty(n-1, p)
  } holds
  
  

  def decreaseLots(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(n >= 0 && i >= 0 && i <= n && checkProperty(n, p))

    if (i >= n-1) {
      checkProperty(i, p)
    } else {
      decreaseLots(n-1, p, i)
      checkProperty(i, p)
    }
  } holds
  
  
  def instantiate(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(n >= 0 && checkProperty(n, p) && i >= 0 && i < n)
    
    decreaseLots(n, p, i+1) && // lemma application
    p(i)
  } holds
  
  
  def thh(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    require(networkInvariant(param, states, messages, getActor))
    
    val Size(n) = param
    checkProperty(n, (i: BigInt) => getActor.contains(UID(i)))
  } holds
  
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    val Size(n) = param
    n > 1  &&
    checkProperty(n, (i: BigInt) => states.contains(UID(i))) &&
    checkProperty(n, (i: BigInt) => getActor.contains(UID(i))) && 
    checkProperty(n, (i: BigInt) => getActor(UID(i)).myId == UID(i)) &&
    checkProperty(n, (i: BigInt) => 
      checkProperty(n, (j: BigInt) => 
        messages.contains(UID(i),UID(j)) ==> (j == increment(i,n)) &&
        ((states(UID(i)), states(UID(j))) match {
          case (KnowLeader(a), KnowLeader(b)) => a == b
          case _ => true
        })
      )
    )
  }
  
  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    
    val sms = net.messages.getOrElse((sender, receiver), Nil())
    
    val Size(n) = net.param
  
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = net.messages.updated((sender, receiver), xs)
        
        val UID(usender) = sender
        val UID(ureceiver) = receiver 
        
        0 <= usender && usender < n && 
        ureceiver == increment(usender,n) && 
        instantiate(n, (i: BigInt) => net.getActor.contains(UID(i)), ureceiver) &&
        net.getActor.contains(receiver)
      case _ => 
        true
    }
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