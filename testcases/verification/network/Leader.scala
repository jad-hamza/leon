package distribution


import FifoNetwork._
import Networking._
import ProtocolProof._
import Quantifiers._

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
  
  

  case class Process(myId: ActorId, ssn: BigInt) extends Actor {
    val UID(myuid) = myId
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
      val Params(n, starterProcess, ssns) = net.param
    
      if (myuid == starterProcess) {
        val nextProcess = UID(increment(myuid, n))
        update(Participant())
        !! (nextProcess, Election(ssn))
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
      
      val Params(n, starterProcess, ssns) = net.param
      val nextProcess = UID(increment(myuid, n))
    
      (sender, m, state) match {
        case (id, Election(ssn2), NonParticipant()) =>
          if (ssn != ssn2) {
            val packet = if (ssn > ssn2) Election(ssn) else Election(ssn2)  
            
            update (Participant())
            !! (nextProcess, packet)
          }
          else {
            // I cannot receive an Election message equal to my ssn if I'm not a participant
//             assert(false)
            ()
          }
          
        case (id, Election(ssn2), Participant()) =>
          if (ssn2 > ssn) {
            !! (nextProcess, Election(ssn2))
          } else if (ssn == ssn2) {
            update (KnowLeader(ssn))
            !! (nextProcess, Elected(ssn))
            // I'm the leader!!
          } else {
            // discard smaller ssn Election message
          }
          
        case (id, Elected(ssn2), Participant()) => {
          update (KnowLeader(ssn2))
          !! (nextProcess, Elected(ssn2))
        }
          
        case (id, Elected(_), NonParticipant()) =>
          // I cannot receive an Elected message if I didn't even participate yet
//           assert(false)
            ()
        
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

