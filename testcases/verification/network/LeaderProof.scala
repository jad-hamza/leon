package distribution


import FifoNetwork._
import Networking._
import IntQuantifiers._
import Protocol._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  
  def validParam(p: Parameter) = {
    val Params(n, starter) = p
    0 <= starter && starter < n
  }
  
  def validGetActor(net: VerifiedNetwork, id: ActorId) = {
    require(
      networkInvariant(net.param, net.states, net.messages, net.getActor) && 
      validId(net,id)
    )
    
    val UID(uid) = id
    val Params(n,_) = net.param
    
    elimForAll(n, getActorDefined(net.getActor), uid) && 
    net.getActor.contains(id)
  } holds
  
  
  def validId(net: VerifiedNetwork, id: ActorId) = {
    require(networkInvariant(net.param, net.states, net.messages, net.getActor))
    val UID(uid) = id
    val Params(n, _) = net.param
    0 <= uid && uid < n
  }
  
  /**
   * Invariant stating that the getActor map is defined for all actors, 
   * and that getActor(i) has id "i"
   */
  
  
  def getActorDefined(getActor: MMap[ActorId,Actor])(i: BigInt) = {
    getActor.contains(UID(i)) && getActor(UID(i)) == Process(UID(i))
  }
   
  
  def init_getActorDefined(n: BigInt): Boolean = {
    
    if (n <= 0) intForAll(n, getActorDefined(init_getActor))
    else init_getActorDefined(n-1) && intForAll(n, getActorDefined(init_getActor))
    
  } holds
  
  
  /**
   * Invariant stating that the states map is defined for all actors
   */
  
  
  def statesDefined(states: MMap[ActorId,State]) = {
    (i: BigInt) => states.contains(UID(i))
  }
  
  def init_statesDefined(n: BigInt): Boolean = {
    
    if (n <= 0) intForAll(n, statesDefined(init_states))
    else init_statesDefined(n-1) && init_states.contains(UID(n-1)) && intForAll(n, statesDefined(init_states))
    
  } holds
  
  
  def statesStillDefined(n: BigInt, states: MMap[ActorId,State], id: ActorId, s: State): Boolean = {
    require(intForAll(n, statesDefined(states)))
    
    if (n <= 0) 
      intForAll(n, statesDefined(states.updated(id,s)))
    else 
      states.updated(id,s).contains(UID(n-1)) && 
      statesStillDefined(n-1, states, id,  s) && 
      intForAll(n, statesDefined(states.updated(id,s)))
  
  } holds
  
  
  /**
   * Invariant stating that communication only happens in rings
   */
  
  def ringChannels(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]])(i: BigInt, j: BigInt) = {
    0 <= i && i < n && (messages.contains(UID(i),UID(j)) ==> (j == increment(i,n)))
  }
  
  def init_ringChannels_aux(u: BigInt, v: BigInt, n: BigInt): Boolean =  {
    require(u <= n && v <= n)
    
    if (u <= 0 || v <= 0) 
      intForAll2(u, v, ringChannels(n, init_messages))
    else {
      init_ringChannels_aux(u-1, v, n) && 
      init_ringChannels_aux(u, v-1, n) && 
      intForAll2(u, v, ringChannels(n, init_messages))
    }
  } holds
  
  def init_ringChannels(n: BigInt): Boolean =  {
    init_ringChannels_aux(n, n, n) &&
    intForAll2(n, n, ringChannels(n, init_messages))
  } holds
  
  def stillRingChannels(
      n: BigInt, m1: BigInt, m2: BigInt, messages: MMap[(ActorId,ActorId),List[Message]], 
      usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {
    
    require(
      m1 <= n && m2 <= n && 
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      intForAll2(m1, m2, ringChannels(n, messages)) && ureceiver == increment(usender, n))
    
    if (m1 <= 0 || m2 <= 0) 
      intForAll2(m1, m2, ringChannels(n, messages.updated((UID(usender),UID(ureceiver)), tt)))
    else 
      stillRingChannels(n, m1-1, m2, messages, usender, ureceiver, tt) &&
      stillRingChannels(n, m1, m2-1, messages, usender, ureceiver, tt) &&
      intForAll2(m1, m2, ringChannels(n, messages.updated((UID(usender),UID(ureceiver)), tt)))
    
  } holds
  
  
  /**
   * Invariant stating that each channel contains at most one message
   */
  
  def smallChannel(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]])(i: BigInt) = {
    0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).size < 2
  }
 
  def init_smallChannel_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n)
    if (u <= 0)
      intForAll(u, smallChannel(n, init_messages))
    else
      init_smallChannel_aux(u-1, n) && 
      intForAll(u, smallChannel(n, init_messages))
  } holds
  
  def init_smallChannel(n: BigInt) = init_smallChannel_aux(n,n)
  
  
  def stillSmallChannel(
      n: BigInt, m: BigInt, messages: MMap[(ActorId,ActorId),List[Message]], 
      usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {
    require(
      m <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      tt.size < 2 &&
      intForAll(m, smallChannel(n, messages)))
    
    if (m <= 0) 
      intForAll(m, smallChannel(n, messages.updated((UID(usender),UID(ureceiver)), tt)))
    else 
      stillSmallChannel(n, m-1, messages, usender, ureceiver, tt) &&
      intForAll(m, smallChannel(n, messages.updated((UID(usender),UID(ureceiver)), tt)))
    
  } holds
  
  
  /**
   * Invariant stating that there is at most channel which is not empty
   */
  
  def onlyOneChannel(n: BigInt, messages:MMap[(ActorId,ActorId), List[Message]])(i: BigInt, j: BigInt) = {
    0 <= i && i < n &&
    0 <= j && j < n &&
    (
      messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).isEmpty || 
      messages.getOrElse((UID(j), UID(increment(j,n))), Nil()).isEmpty
    )
  }
  
  def init_onlyOneChannel_aux(u: BigInt, v: BigInt, n: BigInt): Boolean =  {
    require(u <= n && v <= n)
    
    if (u <= 0 || v <= 0) 
      intForAll2(u, v, onlyOneChannel(n, init_messages))
    else {
      init_onlyOneChannel_aux(u-1, v, n) && 
      init_onlyOneChannel_aux(u, v-1, n) && 
      onlyOneChannel(n, init_messages)(u-1,v-1) &&
      intForAll2(u, v, onlyOneChannel(n, init_messages))
    }
  } holds
//   
  def init_onlyOneChannel(n: BigInt) = init_onlyOneChannel_aux(n,n,n)
  
  
  
  def onlyOneLeader(n: BigInt, states: MMap[ActorId,State]) = {
    require(intForAll(n, statesDefined(states)))
    
    (i: BigInt, j: BigInt) => {
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      0 <= j && j < n && elimForAll(n, statesDefined(states), j) &&
      ((states(UID(i)), states(UID(j))) match {
        case (KnowLeader(a), KnowLeader(b)) => a == b
        case _ => true
      })
      
    }
  }
  
  def noLeaderDuringElection(n: BigInt, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]]) = {
    require(intForAll(n, statesDefined(states)))
    
  
    (i: BigInt, j: BigInt) =>
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      0 <= j && j < n && elimForAll(n, statesDefined(states), j) &&
      (existsMessage(n, messages, Election(i)) ==> (
        states(UID(i)) == Participant() &&
        (states(UID(j)) match {
          case KnowLeader(_) => false
          case _ => true
        })
      ))
  }
  
  
  def everyOneParticipated(n: BigInt, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]]) = {
    require(intForAll(n, statesDefined(states)))
    
  
    (i: BigInt, j: BigInt) =>
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      0 <= j && j < n && elimForAll(n, statesDefined(states), j) &&
      (existsMessage(n, messages, Elected(i)) ==>  (
        states(UID(i)) == KnowLeader(i) &&
        (states(UID(j)) match {
          case KnowLeader(i2) => i == i2
          case NonParticipant() => false
          case Participant() => true
        })))
  }
  
  
  
  /**
   * Property (not invariant) stating that all channels are empty
   */
  
  def emptyChannel(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]])(i: BigInt) = {
    0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).isEmpty
  }
 
  def init_emptyChannel_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n)
    if (u <= 0)
      intForAll(u, emptyChannel(n, init_messages))
    else
      init_emptyChannel_aux(u-1, n) && 
      intForAll(u, emptyChannel(n, init_messages))
  } holds
  
  def init_emptyChannel(n: BigInt) = init_emptyChannel_aux(n,n)
  
  
  
  /**
   * Making initial network
   */
  
  def init_states_fun(id: ActorId): Option[State] = Some(NonParticipant())
  def init_getActor_fun(id: ActorId): Option[Actor] = Some(Process(id))
  def init_messages_fun(ids: (ActorId,ActorId)): Option[List[Message]] = None()
  
  val init_states = MMap(init_states_fun)
  val init_getActor = MMap(init_getActor_fun)
  val init_messages = MMap(init_messages_fun)
  

  def makeNetwork(p: Parameter) = {
    require {
      val Params(n, starterProcess) = p
      validParam(p) &&
      init_statesDefined(n) && 
      init_getActorDefined(n) && 
      init_ringChannels(n) && 
      init_smallChannel(n) && 
      init_emptyChannel(n) && 
      init_onlyOneChannel(n) && 
      intForAll(n, statesDefined(init_states)) &&
      intForAll(n, getActorDefined(init_getActor)) &&
      intForAll2(n, n, ringChannels(n, init_messages)) &&
      intForAll(n, smallChannel(n, init_messages)) &&
      intForAll(n, emptyChannel(n, init_messages)) &&
      intForAll2(n, n, onlyOneChannel(n, init_messages))
    }
    
    VerifiedNetwork(p, init_states, init_messages, init_getActor)
  } ensuring(res => networkInvariant(res.param, res.states, res.messages, res.getActor))
  
  
  /**
   * Network Invariant for the class VerifiedNetwork
   */
 
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    val Params(n, starterProcess) = param
    validParam(param) && 
    intForAll(n, getActorDefined(getActor)) &&
    intForAll(n, statesDefined(states)) &&
    intForAll2(n, n, ringChannels(n, messages)) &&
    intForAll(n, smallChannel(n, messages)) &&
    intForAll2(n, n, onlyOneChannel(n, messages))
//     intForAll2(n, n, onlyOneLeader(n, states)) &&
//     intForAll2(n, n, noLeaderDuringElection(n, states, messages)) &&
//     intForAll2(n, n, everyOneParticipated(n, states, messages))
  }
  
  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    require(
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      validId(net, sender) &&
      validId(net, receiver)
    )
//     true
    val sms = net.messages.getOrElse((sender, receiver), Nil())
    
    val Params(n, starterProcess) = net.param
        
    val UID(usender) = sender
    val UID(ureceiver) = receiver 
    
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = net.messages.updated((sender, receiver), xs)
        0 <= usender && usender < n && 
        0 <= ureceiver && ureceiver < n && 
        elimForAll(n, getActorDefined(net.getActor), ureceiver) &&
        net.getActor.contains(receiver) && 
        net.getActor(receiver) == Process(receiver) &&
        intForAll2(n, n, ringChannels(n, net.messages)) &&
        elimForAll2(n, n, ringChannels(n, net.messages), usender, ureceiver) &&
        ureceiver == increment(usender, n) &&
        stillRingChannels(n, n, n, net.messages, usender, ureceiver, xs) &&
        intForAll2(n, n, ringChannels(n, messages2)) && 
        elimForAll(n, smallChannel(n, net.messages), usender) &&
        sms.size < 2 &&
        xs.size < 2 &&
        stillSmallChannel(n, n, net.messages, usender, ureceiver, xs) 
//         &&
//         networkInvariant(net.param, net.states, messages2, net.getActor)
      case _ => 
        true
    }
  } holds
  

  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    val UID(myuid) = a.myId
    val Params(n, starterProcess) = net.param
    val states = net.states
    
    networkInvariant(net.param, net.states, net.messages, net.getActor) && (
    if (myuid == starterProcess) {
      val nextProcess = UID(increment(myuid, n))
      val newStates = net.states.updated(a.myId, Participant())
      val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
      val newChannel = channel :+ Election(myuid)
      val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
      
      0 <= myuid && myuid < n &&
      statesStillDefined(n, states, a.myId, Participant()) &&
      stillRingChannels(n, n, n, net.messages, myuid, increment(myuid,n), newChannel) &&
      networkInvariant(net.param, states.updated(a.myId, Participant()), newMessages, net.getActor)
  //       update(Participant())
  //       !! (nextProcess, Election(myuid))
    }
    else {
      true
    })
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {

    
    val UID(myuid) = a.myId
    val UID(usender) = sender
    val Params(n, starterProcess) = net.param
    val states = net.states
    val messages = net.messages
  
    networkInvariant(net.param, net.states, net.messages, net.getActor)  &&
    0 <= myuid && myuid < n &&  {
      val nextProcess = UID(increment(myuid, n))
      intForAll(n, statesDefined(states)) &&
      elimForAll(n, statesDefined(states), myuid) &&
        ((sender, m, a.state) match {
          case (id, Election(uid), NonParticipant()) =>
            if (uid > myuid) {
//               update (Participant())
//               !! (nextProcess, Election(uid))
              val newStates = states.updated(a.myId, Participant())
              val channel = messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(uid)
              val newMessages = messages.updated((a.myId, nextProcess), newChannel)

              statesStillDefined(n, states, a.myId, Participant())  &&
              stillRingChannels(n, n, n, messages, myuid, increment(myuid,n), newChannel) 
//               &&
//               networkInvariant(net.param, states.updated(a.myId, Participant()), newMessages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
            } 
            else if (uid < myuid) {
//             update (Participant())
//             !! (nextProcess, Election(myuid))
              val newStates = states.updated(a.myId, Participant())
              val channel = messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(myuid)
              val newMessages = messages.updated((a.myId, nextProcess), newChannel)

              statesStillDefined(n, states, a.myId, Participant())  &&
              stillRingChannels(n, n, n, messages, myuid, increment(myuid,n), newChannel) 
//               &&
//               networkInvariant(net.param, states.updated(a.myId, Participant()), newMessages, net.getActor) 
//               &&
//               networkInvariant(net.param, states.updated(a.myId, Participant()), newMessages, net.getActor)
            }
            else {
              // I cannot receive an Election message equal to my uid if I'm not a participant
                true
//               false
            }
            
          case (id, Election(uid), Participant()) =>
            if (uid > myuid) {
//               !! (nextProcess, Election(uid))
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
              
              stillRingChannels(n, n, n, messages, myuid, increment(myuid,n), newChannel)
//               &&
//               networkInvariant(net.param, net.states, newMessages, net.getActor)
            } else if (uid == myuid) {
//               update (KnowLeader(uid))
//               !! (nextProcess, Elected(myuid))
              val newStates = states.updated(a.myId, KnowLeader(uid))
              val channel = messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Elected(myuid)
              val newMessages = messages.updated((a.myId, nextProcess), newChannel)

              statesStillDefined(n, states, a.myId, KnowLeader(uid)) &&
              stillRingChannels(n, n, n, messages, myuid, increment(myuid,n), newChannel)
//               &&
//               networkInvariant(net.param, states.updated(a.myId, KnowLeader(uid)), newMessages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
            } else {
              true
              // discard smaller uid Election message
            }
            
          case (id, Elected(_), NonParticipant()) =>
            // I cannot receive an Elected message if I didn't even participate yet
            true
//             false
            
          case (id, Elected(uid), Participant()) => {
//               update (KnowLeader(uid))
//               !! (nextProcess, Elected(uid))
              val newStates = states.updated(a.myId, KnowLeader(uid))
              val channel = messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Elected(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
              
              statesStillDefined(n, states, a.myId, KnowLeader(uid)) &&
              stillRingChannels(n, n, n, messages, myuid, increment(myuid,n), newChannel) 
//               &&
//               networkInvariant(net.param, states.updated(a.myId, KnowLeader(uid)), newMessages, net.getActor)
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
          }
          
          case (id, Elected(uid), KnowLeader(uid2)) => {
//             uid == uid2
              true
          }
          
          case (id, Election(_), KnowLeader(_)) =>
            // there cannot be an election going on if I already know the Leader
              true
//             false
          
          case _ => {
              true
//             false
          }
        })
    }
  } 
  
  
  def existsMessage(n: BigInt,  messages: MMap[(ActorId,ActorId),List[Message]], m: Message) = {
    require(n >= 0)
    intExists(n, (i: BigInt) => 0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).contains(m))
  }
  
  
  @ignore
  def main(args: Array[String]) = {
//     val net = VerifiedNetwork(
//       
//     )
  }

}