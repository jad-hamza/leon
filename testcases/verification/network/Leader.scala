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
  
  
  def init_states_fun(id: ActorId): Option[State] = Some(NonParticipant())
  def init_getActor_fun(id: ActorId): Option[Actor] = Some(Process(id))
  def init_Messages_fun(ids: (ActorId,ActorId)): Option[List[Message]] = None()
  
  val init_states = MMap(init_states_fun)
  val init_getActor = MMap(init_getActor_fun)
  val init_messages = MMap(init_Messages_fun)
  

  def makeNetwork(p: Parameter) = {
    require {
      val Params(n, starterProcess) = p
      validParam(p) &&
      init_statesDefined(n) && 
      init_getActorDefined(n) && 
      intForAll(n, statesDefined(init_states)) &&
      intForAll(n, getActorDefined(init_getActor))
    }
  
    
    
    VerifiedNetwork(p, init_states, init_messages, init_getActor)
  } ensuring(res => networkInvariant(res.param, res.states, res.messages, res.getActor))
  
  
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
  
}

