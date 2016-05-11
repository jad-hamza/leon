package distribution


import FifoNetwork._
import Networking._
import IntQuantifiers._
import ProtocolProof._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps

// following https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm

object Protocol {
  
  case class Election(i: BigInt) extends Message
  case class Elected(i: BigInt) extends Message

  case class NonParticipant() extends State
  case class Participant() extends State
  case class KnowLeader(i: BigInt) extends State
  
  case class UID(uid: BigInt) extends ActorId
  
  case class Params(n: BigInt, starterProcess: BigInt) extends Parameter
  
  
  def increment(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i < n-1) i+1
    else BigInt(0)
  } ensuring(res => 0 <= res && res < n)
    
  case class Process(myId: ActorId) extends Actor {
    val UID(myuid) = myId
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
      val Params(n, starterProcess) = net.param
    
      if (myuid == starterProcess) {
        val nextProcess = UID(increment(myuid, n))
        update(Participant())
        !! (nextProcess, Election(myuid))
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
      
      val Params(n, starterProcess) = net.param
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
//             assert(false)
            ()
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
          
        case (id, Elected(_), NonParticipant()) =>
          // I cannot receive an Elected message if I didn't even participate yet
//           assert(false)
            ()
          
        case (id, Elected(uid), Participant()) => {
          update (KnowLeader(uid))
          !! (nextProcess, Elected(uid))
        }
        
        case (id, Elected(uid), KnowLeader(uid2)) => {
          ()
//           assert(uid == uid2)
        }
        
        case _ => {
//           assert(false)
          ()
        }
              
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  }
    
    
  @ignore
  def main(args: Array[String]) = {
    val n = BigInt(2)
    def messages_fun(ids: (ActorId,ActorId)) = ids match {
      case (UID(i), UID(j)) => 
        if (i == 0 && j == 1) Some(List[Message](Election(0)))
        else if (i == 1 && j == 0) Some(List[Message](Election(0)))
        else None[List[Message]]()
    }
    val messages = MMap[(ActorId,ActorId), List[Message]](messages_fun _)
    val usender = BigInt(0)
    val ureceiver = BigInt(1)
    
    println(channelsBecomeEmpty(n, n, messages, usender, ureceiver))
  }
  
}

