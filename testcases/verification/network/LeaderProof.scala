package distribution


import FifoNetwork._
import Networking._
import Quantifiers._
import Protocol._
import ListUtils._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof {

  import Protocol._

  def areEqual[T](t1: T, t2: T) = t1 == t2

  case class Params(n: BigInt, starterProcess: BigInt, ssns: BigInt => BigInt) extends Parameter

  def validParam(p: Parameter) = {
    val Params(n, starterProcess, ssns) = p
    0 <= starterProcess && starterProcess < n &&
    intForAll2(n, n, distinctSSN_fun(ssns))
  }

  def validGetActor(net: VerifiedNetwork, id: ActorId) = {
    require(
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      validId(net, id)
    )

    val UID(uid) = id
    val Params(n, starterProcess, ssns) = net.param

    elimForAll(n, getActorDefined(net.getActor), uid) &&
    net.getActor.contains(id)
  } holds


  def validId(net: VerifiedNetwork, id: ActorId) = {
    require(networkInvariant(net.param, net.states, net.messages, net.getActor))
    val UID(uid) = id
    val Params(n, starterProcess, ssns) = net.param
    0 <= uid && uid < n
  }

  /**
    * Invariant stating that the getActor map is defined for all actors,
    * and that getActor(i) has id "i"
    */


  def getActorDefined(getActor: MMap[ActorId, Actor])(i: BigInt) = {
    getActor.contains(UID(i)) && getActor(UID(i)).myId == UID(i)
  }


  def init_getActorDefined(n: BigInt, ssns: BigInt => BigInt): Boolean = {

    if (n <= 0) intForAll(n, getActorDefined(init_getActor(ssns)))
    else init_getActorDefined(n - 1, ssns) && intForAll(n, getActorDefined(init_getActor(ssns)))

  } holds


  /**
    * Invariant stating that the states map is defined for all actors
    */


  def statesDefined(states: MMap[ActorId, State]) = {
    (i: BigInt) => states.contains(UID(i))
  }

  def init_statesDefined(n: BigInt): Boolean = {

    if (n <= 0) intForAll(n, statesDefined(init_states))
    else init_statesDefined(n - 1) && init_states.contains(UID(n - 1)) && intForAll(n, statesDefined(init_states))

  } holds


  def statesStillDefined(n: BigInt, states: MMap[ActorId, State], id: ActorId, s: State): Boolean = {
    require(intForAll(n, statesDefined(states)))

    if (n <= 0)
      intForAll(n, statesDefined(states.updated(id, s)))
    else
      states.updated(id, s).contains(UID(n - 1)) &&
      statesStillDefined(n - 1, states, id, s) &&
      intForAll(n, statesDefined(states.updated(id, s)))

  } holds


  /**
    * Invariant stating that communication only happens in rings
    */

  def ringChannels(n: BigInt, messages: MMap[(ActorId, ActorId), List[Message]])(i: BigInt, j: BigInt) = {
    0 <= i && i < n && (messages.contains(UID(i), UID(j)) ==> (j == increment(i, n)))
  }

  def init_ringChannels_aux(u: BigInt, v: BigInt, n: BigInt): Boolean = {
    require(u <= n && v <= n)

    if (u <= 0 || v <= 0)
      intForAll2(u, v, ringChannels(n, init_messages))
    else {
      init_ringChannels_aux(u - 1, v, n) &&
      init_ringChannels_aux(u, v - 1, n) &&
      intForAll2(u, v, ringChannels(n, init_messages))
    }
  } holds

  def init_ringChannels(n: BigInt): Boolean = {
    init_ringChannels_aux(n, n, n) &&
    intForAll2(n, n, ringChannels(n, init_messages))
  } holds

  def stillRingChannels(
    n: BigInt, m1: BigInt, m2: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {

    require(
      m1 <= n && m2 <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      intForAll2(m1, m2, ringChannels(n, messages)) && ureceiver == increment(usender, n))

    if (m1 <= 0 || m2 <= 0)
      intForAll2(m1, m2, ringChannels(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      stillRingChannels(n, m1 - 1, m2, messages, usender, ureceiver, tt) &&
      stillRingChannels(n, m1, m2 - 1, messages, usender, ureceiver, tt) &&
      intForAll2(m1, m2, ringChannels(n, messages.updated((UID(usender), UID(ureceiver)), tt)))

  } holds


  /**
    * Invariant stating that each channel contains at most one message
    */

  def smallChannel(n: BigInt, messages: MMap[(ActorId, ActorId), List[Message]])(i: BigInt) = {
    0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i, n))), Nil()).size < 2
  }

  def init_smallChannel_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n)
    if (u <= 0)
      intForAll(u, smallChannel(n, init_messages))
    else
      init_smallChannel_aux(u - 1, n) &&
      intForAll(u, smallChannel(n, init_messages))
  } holds

  def init_smallChannel(n: BigInt) = init_smallChannel_aux(n, n)


  def stillSmallChannel(
    n: BigInt, m: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {
    require(
      m <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      tt.size < 2 &&
      intForAll(m, smallChannel(n, messages)))

    if (m <= 0)
      intForAll(m, smallChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      stillSmallChannel(n, m - 1, messages, usender, ureceiver, tt) &&
      intForAll(m, smallChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))

  } holds


  def emptyToSmallChannel(
    n: BigInt, m: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {
    require(
      m <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      tt.size < 2 &&
      intForAll(m, emptyChannel(n, messages))
    )

    if (m <= 0)
      intForAll(m, smallChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      emptyToSmallChannel(n, m - 1, messages, usender, ureceiver, tt) &&
      intForAll(m, smallChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))

  } holds


  /**
    * Invariant stating that there is at most channel which is not empty
    */

  def onlyOneChannel(n: BigInt, messages: MMap[(ActorId, ActorId), List[Message]])(i: BigInt, j: BigInt) = {
    0 <= i && i < n &&
    0 <= j && j < n && (
      messages.getOrElse((UID(i), UID(increment(i, n))), Nil()).isEmpty ||
      messages.getOrElse((UID(j), UID(increment(j, n))), Nil()).isEmpty ||
      i == j
      )
  }

  def init_onlyOneChannel_aux(u: BigInt, v: BigInt, n: BigInt): Boolean = {
    require(u <= n && v <= n)

    if (u <= 0 || v <= 0)
      intForAll2(u, v, onlyOneChannel(n, init_messages))
    else {
      init_onlyOneChannel_aux(u - 1, v, n) &&
      init_onlyOneChannel_aux(u, v - 1, n) &&
      onlyOneChannel(n, init_messages)(u - 1, v - 1) &&
      intForAll2(u, v, onlyOneChannel(n, init_messages))
    }
  } holds

  //
  def init_onlyOneChannel(n: BigInt) = init_onlyOneChannel_aux(n, n, n)

  def stillOneChannel(
    n: BigInt, m1: BigInt, m2: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {

    require(
      m1 <= n && m2 <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      !messages.getOrElse((UID(usender), UID(ureceiver)), Nil()).isEmpty &&
      intForAll2(m1, m2, onlyOneChannel(n, messages)) &&
      ureceiver == increment(usender, n))

    if (m1 <= 0 || m2 <= 0)
      intForAll2(m1, m2, onlyOneChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      stillOneChannel(n, m1 - 1, m2, messages, usender, ureceiver, tt) &&
      stillOneChannel(n, m1, m2 - 1, messages, usender, ureceiver, tt) &&
      intForAll2(m1, m2, onlyOneChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))

  } holds

  def emptyToOneChannel(
    n: BigInt, m1: BigInt, m2: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {

    require(
      m1 <= n && m2 <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      intForAll(n, emptyChannel(n, messages)) &&
      ureceiver == increment(usender, n))

    if (m1 <= 0 || m2 <= 0)
      intForAll2(m1, m2, onlyOneChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      elimForAll(n, emptyChannel(n, messages), m1 - 1) &&
      elimForAll(n, emptyChannel(n, messages), m2 - 1) &&
      onlyOneChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt))(m1 - 1, m2 - 1) &&
      emptyToOneChannel(n, m1 - 1, m2, messages, usender, ureceiver, tt) &&
      emptyToOneChannel(n, m1, m2 - 1, messages, usender, ureceiver, tt) &&
      intForAll2(m1, m2, onlyOneChannel(n, messages.updated((UID(usender), UID(ureceiver)), tt)))
  } holds


  /**
    * Invariant stating that if there is an Election message in transit, then
    * no one can know the leader
    */

  def noLeaderDuringElection(n: BigInt, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]]) = {
    require(intForAll(n, statesDefined(states)))


    (i: BigInt) =>
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      (existsMessage(n, messages, isElectionMessage) ==> !isKnowLeaderState(states(UID(i))))
  }

  def init_noLeaderDuringElection_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n)

    if (u <= 0 || n <= 0)
      init_statesDefined(n) &&
      intForAll(u, noLeaderDuringElection(n, init_states, init_messages))
    else {
      n > 0 &&
      init_emptyChannel(n) &&
      nothingExists(n, init_messages, isElectionMessage) &&
      !existsMessage(n, init_messages, isElectionMessage) &&
      init_statesDefined(n) &&
      noLeaderDuringElection(n, init_states, init_messages)(u - 1) &&
      init_noLeaderDuringElection_aux(u - 1, n) &&
      intForAll(u, noLeaderDuringElection(n, init_states, init_messages))
    }
  } holds

  def init_noLeaderDuringElection(n: BigInt) = init_noLeaderDuringElection_aux(n, n)

  def stillnoLeaderDuringElection(
    n: BigInt, u: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt, tt: List[Message]): Boolean = {

    require(
      u <= n &&
      0 <= usender && usender < n &&
      0 <= ureceiver && ureceiver < n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeaderDuringElection(n, states, messages)) &&
      ureceiver == increment(usender, n) &&
      !contains(tt, isElectionMessage)
    )

    if (u <= 0)
      intForAll(u, noLeaderDuringElection(n, states, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else if (existsMessage(n, messages, isElectionMessage))
      elimForAll(n, noLeaderDuringElection(n, states, messages), u - 1) &&
      stillnoLeaderDuringElection(n, u - 1, states, messages, usender, ureceiver, tt) &&
      intForAll(u, noLeaderDuringElection(n, states, messages.updated((UID(usender), UID(ureceiver)), tt)))
    else
      updateChannel(n, messages, tt, isElectionMessage, usender, ureceiver) &&
      stillnoLeaderDuringElection(n, u - 1, states, messages, usender, ureceiver, tt) &&
      intForAll(u, noLeaderDuringElection(n, states, messages.updated((UID(usender), UID(ureceiver)), tt)))

  } holds

  /**
    * Invariant stating if two people know the leader, they must agree on
    * the identity
    */

  def onlyOneLeader(n: BigInt, states: MMap[ActorId, State]) = {
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

  /**
    * Invariant stating that if someone knows the leader, then there are no
    * NonParticipant's
    */


  //   def everyOneParticipated(n: BigInt, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]]) = {
  //     require(intForAll(n, statesDefined(states)))
  //
  //
  //     (i: BigInt, j: BigInt) =>
  //       0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
  //       0 <= j && j < n && elimForAll(n, statesDefined(states), j) &&
  //       (existsMessage(n, messages, Elected(i)) ==>  (
  //         states(UID(i)) == KnowLeader(i) &&
  //         (states(UID(j)) match {
  //           case KnowLeader(i2) => i == i2
  //           case NonParticipant() => false
  //           case Participant() => true
  //         })))
  //   }
  //
  /**
    * Invariant stating that ssn's are unique
    */

  def distinctSSN(n: BigInt, getActor: MMap[ActorId, Actor]) = {
    require(intForAll(n, getActorDefined(getActor)))

    (i: BigInt, j: BigInt) =>
      0 <= i && i < n && elimForAll(n, getActorDefined(getActor), i) &&
      0 <= j && j < n && elimForAll(n, getActorDefined(getActor), j) && {
        val Process(id1, ssn1) = getActor(UID(i))
        val Process(id2, ssn2) = getActor(UID(j))
        ssn1 != ssn2 || i == j
      }
  }

  def distinctSSN_fun(ssns: BigInt => BigInt) = {
    (i: BigInt, j: BigInt) => ssns(i) != ssns(j) || i == j
  }


  def init_distinctSSN_aux(n: BigInt, u: BigInt, v: BigInt, ssns: BigInt => BigInt): Boolean = {
    require(u <= n && v <= n && intForAll2(n, n, distinctSSN_fun(ssns)))

    if (u <= 0 || v <= 0 || n <= 0)
      init_getActorDefined(n, ssns) &&
      intForAll2(u, v, distinctSSN(n, init_getActor(ssns)))
    else {
      init_getActorDefined(n, ssns) &&
      init_distinctSSN_aux(n, u - 1, v, ssns) &&
      init_distinctSSN_aux(n, u, v - 1, ssns) &&
      elimForAll2(n, n, distinctSSN_fun(ssns), u - 1, v - 1) &&
      intForAll2(u, v, distinctSSN(n, init_getActor(ssns)))
    }
  } holds


  def init_distinctSSN(n: BigInt, ssns: BigInt => BigInt): Boolean = {
    require(intForAll2(n, n, distinctSSN_fun(ssns)))

    init_distinctSSN_aux(n, n, n, ssns)
  } holds


  /**
    * Property (not invariant) stating that all channels are empty
    */

  def emptyChannel(n: BigInt, messages: MMap[(ActorId, ActorId), List[Message]])(i: BigInt) = {
    0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i, n))), Nil()).isEmpty
  }

  def init_emptyChannel_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n)
    if (u <= 0)
      intForAll(u, emptyChannel(n, init_messages))
    else
      init_emptyChannel_aux(u - 1, n) &&
      intForAll(u, emptyChannel(n, init_messages))
  } holds

  def init_emptyChannel(n: BigInt) = init_emptyChannel_aux(n, n)


  def channelsBecomeEmpty(
    n: BigInt, m: BigInt, messages: MMap[(ActorId, ActorId), List[Message]],
    usender: BigInt, ureceiver: BigInt): Boolean = {
    require(
      intForAll2(n, n, onlyOneChannel(n, messages)) &&
      0 <= usender && usender < n &&
      ureceiver == increment(usender, n) &&
      messages.contains((UID(usender), UID(ureceiver))) &&
      !messages((UID(usender), UID(ureceiver))).isEmpty &&
      m <= n
    )

    if (m <= 0)
      intForAll(m, emptyChannel(n, messages.updated((UID(usender), UID(ureceiver)), Nil())))
    else if (usender == m - 1)
      emptyChannel(n, messages.updated((UID(usender), UID(ureceiver)), Nil()))(m - 1) &&
      channelsBecomeEmpty(n, m - 1, messages, usender, ureceiver) &&
      intForAll(m, emptyChannel(n, messages.updated((UID(usender), UID(ureceiver)), Nil())))
    else
      elimForAll2(n, n, onlyOneChannel(n, messages), usender, m - 1) &&
      emptyChannel(n, messages.updated((UID(usender), UID(ureceiver)), Nil()))(m - 1) &&
      channelsBecomeEmpty(n, m - 1, messages, usender, ureceiver) &&
      intForAll(m, emptyChannel(n, messages.updated((UID(usender), UID(ureceiver)), Nil())))


  } holds

  /**
    * Property stating that there is no leader (yet)
    */

  def noLeader(n: BigInt, states: MMap[ActorId, State]) = {
    require(intForAll(n, statesDefined(states)))

    (i: BigInt) =>
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      !isKnowLeaderState(states(UID(i)))
  }


  def init_noLeader_aux(u: BigInt, n: BigInt): Boolean = {
    require(u <= n && init_statesDefined(n))
    if (u <= 0)
      intForAll(u, noLeader(n, init_states))
    else
      init_noLeader_aux(u - 1, n) &&
      intForAll(u, noLeader(n, init_states))
  } holds

  def init_noLeader(n: BigInt) = init_noLeader_aux(n, n)


  def stillNoLeader_aux(n: BigInt, u: BigInt, states: MMap[ActorId, State], id: BigInt, s: State): Boolean = {
    require(
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states)) &&
      !isKnowLeaderState(s) &&
      u <= n
    )

    if (u <= 0 || n <= 0)
      statesStillDefined(n, states, UID(id), s) &&
      intForAll(u, noLeader(n, states.updated(UID(id), s)))
    else
      elimForAll(n, noLeader(n, states), u - 1) &&
      statesStillDefined(n, states, UID(id), s) &&
      noLeader(n, states.updated(UID(id), s))(u - 1) &&
      stillNoLeader_aux(n, u - 1, states, id, s) &&
      intForAll(u, noLeader(n, states.updated(UID(id), s)))
  } holds

  def stillNoLeader(n: BigInt, states: MMap[ActorId, State], id: BigInt, s: State) = {
    require(
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states)) &&
      !isKnowLeaderState(s)
    )

    stillNoLeader_aux(n, n, states, id, s)
  } holds


  def noLeaderImpliesNoLeaderDuringElection_aux(
    n: BigInt, u: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    require(
      0 <= n && u <= n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states))
    )

    if (u <= 0 || n <= 0)
      intForAll(u, noLeaderDuringElection(n, states, messages))
    else
      elimForAll(n, noLeader(n, states), u - 1) &&
      noLeaderImpliesNoLeaderDuringElection_aux(n, u - 1, states, messages) &&
      intForAll(u, noLeaderDuringElection(n, states, messages))
  } holds


  def noLeaderImpliesNoLeaderDuringElection(
    n: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ) = {
    require(
      0 <= n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states)))

    noLeaderImpliesNoLeaderDuringElection_aux(n, n, states, messages)
  }


  def noElectionImpliesNoLeaderDuringElection_aux(
    n: BigInt, u: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    require(
      0 <= n && u <= n &&
      intForAll(n, statesDefined(states)) &&
      !existsMessage(n, messages, isElectionMessage)
    )

    if (u <= 0 || n <= 0)
      intForAll(u, noLeaderDuringElection(n, states, messages))
    else
      noElectionImpliesNoLeaderDuringElection_aux(n, u - 1, states, messages) &&
      intForAll(u, noLeaderDuringElection(n, states, messages))
  } holds

  def noElectionImpliesNoLeaderDuringElection(
    n: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    require(
      0 <= n &&
      intForAll(n, statesDefined(states)) &&
      !existsMessage(n, messages, isElectionMessage)
    )
    noElectionImpliesNoLeaderDuringElection_aux(n, n, states, messages)
  } holds


  def electionImpliesNoLeader_aux(
    n: BigInt, u: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]): Boolean = {
    require(
      n >= 0 && u <= n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeaderDuringElection(n, states, messages)) &&
      existsMessage(n, messages, isElectionMessage)
    )

    if (u <= 0 || n <= 0)
      intForAll(u, noLeader(n, states))
    else
      elimForAll(n, noLeaderDuringElection(n, states, messages), u - 1) &&
      electionImpliesNoLeader_aux(n, u - 1, states, messages) &&
      intForAll(u, noLeader(n, states))
  } holds

  def electionImpliesNoLeader(n: BigInt, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]]) = {
    require(
      n >= 0 &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeaderDuringElection(n, states, messages)) &&
      existsMessage(n, messages, isElectionMessage)
    )
    electionImpliesNoLeader_aux(n, n, states, messages)
  }

  /**
    * Making initial network
    */

  def init_states_fun(id: ActorId): Option[State] = Some(NonParticipant())

  def init_getActor_fun(ssns: BigInt => BigInt) = {
    require(true)

    (id: ActorId) => {
      val UID(uid) = id
      Some(Process(id, ssns(uid))): Option[Actor]
    }
  }

  def init_messages_fun(ids: (ActorId, ActorId)): Option[List[Message]] = None()

  val init_states = MMap(init_states_fun)
  val init_messages = MMap(init_messages_fun)

  def init_getActor(ssns: BigInt => BigInt) = {
    require(true)

    MMap(init_getActor_fun(ssns))
  }


  def makeNetwork(p: Parameter) = {
                                    require {
                                      val Params(n, starterProcess, ssns) = p
                                      validParam(p) &&
                                      init_statesDefined(n) &&
                                      init_getActorDefined(n, ssns) &&
                                      init_ringChannels(n) &&
                                      init_smallChannel(n) &&
                                      init_emptyChannel(n) &&
                                      init_onlyOneChannel(n) &&
                                      init_noLeaderDuringElection(n) &&
                                      init_noLeader(n) &&
                                      init_distinctSSN(n, ssns) &&
                                      init_electingMax(n, starterProcess, ssns) &&
                                      init_electedMax(n, starterProcess, ssns) &&
                                      init_electionParticipants_aux(n, starterProcess) &&
                                      noLeaderImpliesknowTrueLeader(n, starterProcess, init_states, init_getActor(ssns)) &&
                                      intForAll(n, statesDefined(init_states)) &&
                                      intForAll(n, getActorDefined(init_getActor(ssns))) &&
                                      intForAll2(n, n, ringChannels(n, init_messages)) &&
                                      intForAll(n, smallChannel(n, init_messages)) &&
                                      intForAll(n, emptyChannel(n, init_messages)) &&
                                      intForAll2(n, n, onlyOneChannel(n, init_messages)) &&
                                      intForAll(n, noLeaderDuringElection(n, init_states, init_messages)) &&
                                      intForAll(n, noLeader(n, init_states)) &&
                                      intForAll2(n, n, distinctSSN(n, init_getActor(ssns))) &&
                                      intForAll(n, electingMax(n, starterProcess, init_messages, init_getActor(ssns))) &&
                                      intForAll(n, electedMax(n, starterProcess, init_messages, init_getActor(ssns))) &&
                                      intForAll(n, electionParticipants(n, starterProcess, init_states, init_messages)) &&
                                      intForAll(n, knowTrueLeader(n, starterProcess, init_states, init_getActor(ssns)))
                                    }

                                    val Params(n, starterProcess, ssns) = p
                                    VerifiedNetwork(p, init_states, init_messages, init_getActor(ssns))
                                  } ensuring (res => networkInvariant(res.param, res.states, res.messages, res.getActor))


  def inBetween(n: BigInt, i: BigInt, j: BigInt, k: BigInt) = {
    0 <= i && i < n &&
    0 <= j && j < n &&
    0 <= k && k < n && (
      (i <= k && k <= j) ||
      (i > j && k >= i) ||
      (i > j && k <= j)
      )
  }

  def incrementBetween(n: BigInt, i: BigInt, j: BigInt) = {
    require(0 <= j && j < n && inBetween(n, i, j, increment(j, n)))

    increment(j, n) == i
  } holds

  def maxGreater(n: BigInt, i: BigInt, j: BigInt, k: BigInt, getActor: MMap[ActorId, Actor]): Boolean = {
    require(
      intForAll(n, getActorDefined(getActor)) &&
      inBetween(n, i, j, k) && elimForAll(n, getActorDefined(getActor), k))

    val Process(_, ssn) = getActor(UID(k))

    if (i == j) ssn <= collectMaxSSN(n, i, j, getActor)
    else if (k == j) ssn <= collectMaxSSN(n, i, j, getActor)
    else
      maxGreater(n, i, decrement(j, n), k, getActor) &&
      ssn <= collectMaxSSN(n, i, j, getActor)
  } holds

  def maxExists(n: BigInt, i: BigInt, j: BigInt, getActor: MMap[ActorId, Actor]): BigInt = {
                                                                                             require(
                                                                                               0 <= i && i < n &&
                                                                                               0 <= j && j < n &&
                                                                                               intForAll(n, getActorDefined(getActor)) &&
                                                                                               elimForAll(n, getActorDefined(getActor), j)
                                                                                             )

                                                                                             val Process(_, ssn) = getActor(UID(j))

                                                                                             if (i == j) j
                                                                                             else {
                                                                                               val oldval = collectMaxSSN(n, i, decrement(j, n), getActor)
                                                                                               if (ssn > oldval) j
                                                                                               else maxExists(n, i, decrement(j, n), getActor)
                                                                                             }

                                                                                           } ensuring (res => elimForAll(n, getActorDefined(getActor), res) && {
    val Process(_, ssn) = getActor(UID(res))
    ssn == collectMaxSSN(n, i, j, getActor) &&
    inBetween(n, i, j, res)
  })



  /**
    * Invariant stating that when there is an Election(ssn) message in
    * the channel from i to increment(i,n), then ssn must the the maximum
    * of all ssns of Actors from starterProcess to i included.
    * We only look at the head of the channel because there is at most one
    * message in each channel.
    */


  def electingMax(
    n: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]) = {

    require(
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, getActorDefined(getActor))
    )

    (i: BigInt) =>
      0 <= i && i < n && (
        messages.getOrElse((UID(i), UID(increment(i, n))), Nil()) match {
          case Cons(Election(ssn), xs) =>
            ssn == collectMaxSSN(n, starterProcess, i, getActor) ||
            ssn == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
          case _ => true
        })
  }

  def init_electingMax_aux(
    n: BigInt, u: BigInt, starterProcess: BigInt,
    ssns: BigInt => BigInt): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n && u <= n
    )

    if (u <= 0 || n <= 0)
      init_getActorDefined(n, ssns) &&
      intForAll(u, electingMax(n, starterProcess, init_messages, init_getActor(ssns)))
    else
      init_getActorDefined(n, ssns) &&
      init_emptyChannel(n) &&
      elimForAll(n, emptyChannel(n, init_messages), u - 1) &&
      init_electingMax_aux(n, u - 1, starterProcess, ssns) &&
      intForAll(u, electingMax(n, starterProcess, init_messages, init_getActor(ssns)))

  } holds

  def init_electingMax(
    n: BigInt, starterProcess: BigInt,
    ssns: BigInt => BigInt): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n
    )

    init_electingMax_aux(n, n, starterProcess, ssns)
  } holds


  def emptyChannelsImplyElectingMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      m <= n &&
      intForAll(n, emptyChannel(n, messages)) &&
      intForAll(n, getActorDefined(getActor))
    )


    if (m <= 0 || n <= 0)
      intForAll(m, electingMax(n, starterProcess, messages, getActor))
    else
      emptyChannelsImplyElectingMax(n, m - 1, starterProcess, messages, getActor) &&
      elimForAll(n, emptyChannel(n, messages), m - 1) &&
      intForAll(m, electingMax(n, starterProcess, messages, getActor))
  } holds


  def max(i: BigInt, j: BigInt) = if (i > j) i else j

  def collectMaxSSN(n: BigInt, from: BigInt, to: BigInt, getActor: MMap[ActorId, Actor]): BigInt = {
    require(
      0 <= from && from < n &&
      0 <= to && to < n &&
      intForAll(n, getActorDefined(getActor)) &&
      elimForAll(n, getActorDefined(getActor), to)
    )

    val Process(uid, ssn) = getActor(UID(to))

    if (from == to) {
      ssn
    } else {
      max(collectMaxSSN(n, from, decrement(to, n), getActor), ssn)
    }
  }


  def incrDecr(u: BigInt, n: BigInt) = {
    require(0 <= u && u < n)

    increment(decrement(u, n), n) == u
  } holds

  def stillMax(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    getActor: MMap[ActorId, Actor]): Boolean = {

    require {
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      intForAll(n, getActorDefined(getActor)) &&
      elimForAll(n, getActorDefined(getActor), increment(usender, n))
    }

    val Process(_, ssn2) = getActor(UID(increment(usender, n)))

    printing(intToString(collectMaxSSN(n, starterProcess, usender, getActor)))
    printing(intToString(collectMaxSSN(n, starterProcess, increment(usender, n), getActor)))

    if (starterProcess == increment(usender, n)) true
    else {
      max(collectMaxSSN(n, starterProcess, usender, getActor), ssn2) == collectMaxSSN(n, starterProcess, increment(usender, n), getActor)
    }
  } holds

  def noElectionImpliesElectingMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]
  ): Boolean = {
    require(
      m <= n &&
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, getActorDefined(getActor)) &&
      !existsMessage(n, messages, isElectionMessage))

    if (m <= 0)
      intForAll(m, electingMax(n, starterProcess, messages, getActor))
    else
      noElectionImpliesElectingMax(n, m - 1, starterProcess, messages, getActor) && (
        messages.getOrElse((UID(m - 1), UID(increment(m - 1, n))), Nil()) match {
          case Cons(Election(_), _) =>
            witnessImpliesExists(n, hasMessage(n, messages, isElectionMessage), m - 1) &&
            false
          case _ => true
        }) &&
      intForAll(m, electingMax(n, starterProcess, messages, getActor))


  } holds


  def stillElectingMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    myuid: BigInt,
    value: BigInt): Boolean = {
    require(
      intForAll(n, getActorDefined(getActor)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, emptyChannel(n, messages), myuid) &&
      m <= n &&
      0 <= starterProcess && starterProcess < n && (
        value == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor) ||
        value == collectMaxSSN(n, starterProcess, myuid, getActor)
        )
    )


    if (m <= 0)
      intForAll(m, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(value))), getActor))
    else
      stillElectingMax(n, m - 1, starterProcess, messages, getActor, myuid, value) &&
      elimForAll(n, emptyChannel(n, messages), m - 1) &&
      intForAll(m, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(value))), getActor))
  } holds


  /**
    * Invariant about participant state
    */

  def isParticipant(n: BigInt, states: MMap[ActorId, State]) = {
    require(intForAll(n, statesDefined(states)))

    (i: BigInt) =>
      0 <= i && i < n && elimForAll(n, statesDefined(states), i) &&
      states(UID(i)) == Participant()
  }

  def stillParticipating(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    myuid: BigInt,
    states: MMap[ActorId, State]
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      0 <= myuid && myuid < n &&
      intForAll(n, statesDefined(states)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states))
    )

    if (starterProcess == usender)
      elimForAllModulo(n, starterProcess, usender, isParticipant(n, states), usender) &&
      statesStillDefined(n, states, UID(myuid), Participant()) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states.updated(UID(myuid), Participant())))
    else
      stillParticipating(n, starterProcess, decrement(usender, n), myuid, states) &&
      elimForAllModulo(n, starterProcess, usender, isParticipant(n, states), usender) &&
      isParticipant(n, states)(usender) &&
      statesStillDefined(n, states, UID(myuid), Participant()) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states.updated(UID(myuid), Participant())))
  } holds

  def f(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    myuid: BigInt,
    states: MMap[ActorId, State]
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      0 <= myuid && myuid < n &&
      intForAll(n, statesDefined(states)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states)) &&
      elimForAllModulo(n, starterProcess, usender, isParticipant(n, states), usender) &&
      statesStillDefined(n, states, UID(myuid), Participant())
    )

    stillParticipating(n, starterProcess, usender, myuid, states)
  } holds

  def oneMoreParticipant(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    states: MMap[ActorId, State]
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      intForAll(n, statesDefined(states)) &&
      //      elimForAll(n, statesDefined(states), increment(usender,n)) &&
      isParticipant(n, states)(increment(usender, n)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states))
    )

    forAllModulo(n, starterProcess, increment(usender, n), isParticipant(n, states))

  } holds


  /**
    * Invariant stating that an Elected message always contains the maximal SSN
    */

  def electedMax(
    n: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]) = {

    require(
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, getActorDefined(getActor))
    )

    (i: BigInt) =>
      0 <= i && i < n && (
        messages.getOrElse((UID(i), UID(increment(i, n))), Nil()) match {
          case Cons(Elected(ssn), xs) =>
            ssn == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
          case _ => true
        })
  }

  def init_electedMax_aux(
    n: BigInt, u: BigInt, starterProcess: BigInt,
    ssns: BigInt => BigInt): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n && u <= n
    )

    if (u <= 0 || n <= 0)
      init_getActorDefined(n, ssns) &&
      intForAll(u, electedMax(n, starterProcess, init_messages, init_getActor(ssns)))
    else
      init_getActorDefined(n, ssns) &&
      init_emptyChannel(n) &&
      elimForAll(n, emptyChannel(n, init_messages), u - 1) &&
      init_electedMax_aux(n, u - 1, starterProcess, ssns) &&
      intForAll(u, electedMax(n, starterProcess, init_messages, init_getActor(ssns)))

  } holds

  def init_electedMax(
    n: BigInt, starterProcess: BigInt,
    ssns: BigInt => BigInt): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n
    )

    init_electedMax_aux(n, n, starterProcess, ssns)
  } holds


  def emptyChannelsImplyElectedMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      m <= n &&
      intForAll(n, emptyChannel(n, messages)) &&
      intForAll(n, getActorDefined(getActor))
    )


    if (m <= 0 || n <= 0)
      intForAll(m, electingMax(n, starterProcess, messages, getActor))
    else
      emptyChannelsImplyElectedMax(n, m - 1, starterProcess, messages, getActor) &&
      elimForAll(n, emptyChannel(n, messages), m - 1) &&
      intForAll(m, electedMax(n, starterProcess, messages, getActor))
  } holds

  def noElectedImpliesElectedMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor]
  ): Boolean = {
    require(
      m <= n &&
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, getActorDefined(getActor)) &&
      !existsMessage(n, messages, isElectedMessage))

    if (m <= 0)
      intForAll(m, electedMax(n, starterProcess, messages, getActor))
    else
      noElectedImpliesElectedMax(n, m - 1, starterProcess, messages, getActor) && (
        messages.getOrElse((UID(m - 1), UID(increment(m - 1, n))), Nil()) match {
          case Cons(Elected(_), _) =>
            witnessImpliesExists(n, hasMessage(n, messages, isElectedMessage), m - 1) &&
            false
          case _ => true
        }) &&
      intForAll(m, electedMax(n, starterProcess, messages, getActor))


  } holds


  def stillElectedMax(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    myuid: BigInt,
    value: BigInt): Boolean = {
    require(
      intForAll(n, getActorDefined(getActor)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, emptyChannel(n, messages), myuid) &&
      m <= n &&
      0 <= starterProcess && starterProcess < n &&
      value == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
    )


    if (m <= 0)
      intForAll(m, electedMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(value))), getActor))
    else
      stillElectedMax(n, m - 1, starterProcess, messages, getActor, myuid, value) &&
      elimForAll(n, emptyChannel(n, messages), m - 1) &&
      intForAll(m, electedMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(value))), getActor))
  } holds

  /**
    *
    */

  def substitute(n: BigInt, starterProcess: BigInt, usender: BigInt, states1: MMap[ActorId, State], states2: MMap[ActorId, State]) = {
    require(
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      intForAll(n, statesDefined(states2)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states2)) && states1 == states2)


    forAllModulo(n, starterProcess, usender, isParticipant(n, states1))
  } holds


  /**
    * Main invariant stating that if some Actor is in state KnowLeader(ssn) then
    * ssn == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
    * i.e. ssn is the maximum of all SSNs of Actors
    */

  def knowTrueLeader(n: BigInt, starterProcess: BigInt, states: MMap[ActorId,State], getActor: MMap[ActorId,Actor]) = {
    require(
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, getActorDefined(getActor))
    )

    (i: BigInt) =>
      0 <= i && i < n &&
      elimForAll(n, statesDefined(states), i) && (
        states(UID(i)) match {
          case KnowLeader(ssn) => ssn == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
          case _ => true
        })
  }


  def noLeaderImpliesknowTrueLeader_aux(
    n: BigInt, u: BigInt,
    starterProcess: BigInt,
    states: MMap[ActorId, State],
    getActor: MMap[ActorId, Actor]
  ): Boolean = {
    require(
      0 <= n && u <= n &&
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states)) &&
      intForAll(n, getActorDefined(getActor))
    )

    if (u <= 0 || n <= 0)
      intForAll(u, knowTrueLeader(n, starterProcess, states, getActor))
    else
      elimForAll(n, noLeader(n, states), u - 1) &&
      noLeaderImpliesknowTrueLeader_aux(n, u - 1, starterProcess, states, getActor) &&
      intForAll(u, knowTrueLeader(n, starterProcess, states, getActor))
  } holds

  def noLeaderImpliesknowTrueLeader(n: BigInt, starterProcess: BigInt, states: MMap[ActorId, State], getActor: MMap[ActorId,Actor]): Boolean = {
    require(
      0 <= n &&
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, noLeader(n, states)) &&
      intForAll(n, getActorDefined(getActor))
    )
    noLeaderImpliesknowTrueLeader_aux(n, n, starterProcess, states, getActor)
  }

  def stillKnowingTrueLeader(
    n: BigInt,
    u: BigInt,
    starterProcess: BigInt,
    states: MMap[ActorId,State],
    getActor: MMap[ActorId,Actor],
    myuid: BigInt,
    ssn: BigInt
  ): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      u <= n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, getActorDefined(getActor)) &&
      intForAll(n, knowTrueLeader(n, starterProcess, states, getActor)) &&
      ssn == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
    )

    if (u <= 0)
      statesStillDefined(n, states, UID(myuid), KnowLeader(ssn)) &&
      intForAll(u, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn)), getActor))
    else
      statesStillDefined(n, states, UID(myuid), KnowLeader(ssn)) &&
      stillKnowingTrueLeader(n,u-1,starterProcess,states,getActor,myuid,ssn) &&
      elimForAll(n, knowTrueLeader(n, starterProcess, states, getActor), u-1) &&
      intForAll(u, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn)), getActor))

  } holds

  /**
    * Invariant stating that an election message in the channel from
    * j to increment(j,n) implies that all actors between starterProcess
    * and j are in Participant state
    */

  def electionParticipants(
    n: BigInt,
    starterProcess: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]) = {
    require(
      0 <= starterProcess && starterProcess < n &&
      intForAll(n, statesDefined(states))
    )

    (i: BigInt) => {
      0 <= i && i < n && (
        messages.getOrElse((UID(i), UID(increment(i, n))), Nil()) match {
          case Cons(Election(_), _) => forAllModulo(n, starterProcess, i, isParticipant(n, states))
          case _ => true
        })
    }
  }


  def init_electionParticipants_aux(n: BigInt, starterProcess: BigInt): Boolean = {
    require(0 <= starterProcess && starterProcess < n)

    init_statesDefined(n) &&
    init_emptyChannel(n) &&
    emptyChannelsImplyElectionParticipants(n, n, starterProcess, init_states, init_messages)
  } holds

  def emptyChannelsImplyElectionParticipants(
    n: BigInt,
    u: BigInt,
    starterProcess: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]): Boolean = {
    require(
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      0 <= starterProcess && starterProcess < n &&
      u <= n
    )

    if (u <= 0)
      intForAll(u, electionParticipants(n, starterProcess, states, messages))
    else
      emptyChannelsImplyElectionParticipants(n, u - 1, starterProcess, states, messages) &&
      elimForAll(n, emptyChannel(n, messages), u - 1) &&
      intForAll(u, electionParticipants(n, starterProcess, states, messages))
  } holds


  def stillElectionParticipants(
    n: BigInt,
    m: BigInt,
    starterProcess: BigInt,
    myuid: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    tt: List[Message]
  ): Boolean = {
    require(
      m <= n &&
      0 <= starterProcess && starterProcess < n &&
      0 <= myuid && myuid < n &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      forAllModulo(n, starterProcess, myuid, isParticipant(n, states))
    )

    if (m <= 0)
      intForAll(m, electionParticipants(n, starterProcess, states, messages.updated((UID(myuid), UID(increment(myuid, n))), tt)))
    else
      stillElectionParticipants(n, m - 1, starterProcess, myuid, states, messages, tt) &&
      elimForAll(n, emptyChannel(n, messages), m - 1) &&
      intForAll(m, electionParticipants(n, starterProcess, states, messages.updated((UID(myuid), UID(increment(myuid, n))), tt)))
  } holds


  def electionParticipantsLemma(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    myuid: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    newChannel: List[Message]): Boolean = {
    require(
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      0 <= myuid && myuid < n &&
      myuid == increment(usender, n) &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states))
    )
    stillParticipating(n, starterProcess, usender, myuid, states) &&
    forAllModulo(n, starterProcess, usender, isParticipant(n, states.updated(UID(myuid), Participant()))) &&
    oneMoreParticipant(n, starterProcess, usender, states.updated(UID(myuid), Participant())) &&
    forAllModulo(n, starterProcess, increment(usender, n), isParticipant(n, states.updated(UID(myuid), Participant()))) &&
    stillElectionParticipants(n, n, starterProcess, myuid, states.updated(UID(myuid), Participant()), messages, newChannel) &&
    intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), messages.updated((UID(myuid), UID(increment(myuid, n))), newChannel)))

  } holds


  def noElectionImpliesElectionParticipants(
    n: BigInt, m: BigInt,
    starterProcess: BigInt,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {

    require(
      0 <= starterProcess && starterProcess < n &&
      m <= n &&
      intForAll(n, statesDefined(states)) &&
      !existsMessage(n, messages, isElectionMessage)
    )
    if (m <= 0)
      intForAll(m, electionParticipants(n, starterProcess, states, messages))
    else
      noElectionImpliesElectionParticipants(n, m - 1, starterProcess, states, messages) && (
        messages.getOrElse((UID(m - 1), UID(increment(m - 1, n))), Nil()) match {
          case Cons(Election(_), _) => witnessImpliesExists(n, hasMessage(n, messages, isElectionMessage), m - 1) && false
          case _ => true
        }) &&
      intForAll(m, electionParticipants(n, starterProcess, states, messages))
  } holds

  /**
    * Network Invariant for the class VerifiedNetwork
    */

  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId, ActorId), List[Message]], getActor: MMap[ActorId, Actor]) = {
    val Params(n, starterProcess, ssns) = param
    validParam(param) &&
    intForAll(n, getActorDefined(getActor)) &&
    intForAll(n, statesDefined(states)) &&
    intForAll2(n, n, ringChannels(n, messages)) &&
    intForAll(n, smallChannel(n, messages)) &&
    intForAll2(n, n, onlyOneChannel(n, messages)) &&
    intForAll(n, noLeaderDuringElection(n, states, messages)) &&
    intForAll2(n, n, distinctSSN(n, getActor)) &&
    intForAll(n, electingMax(n, starterProcess, messages, getActor)) &&
    intForAll(n, electedMax(n, starterProcess, messages, getActor)) &&
    intForAll(n, electionParticipants(n, starterProcess, states, messages)) &&
    intForAll(n, knowTrueLeader(n, starterProcess, states, getActor))
  }

  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    require(
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      validId(net, sender) &&
      validId(net, receiver)
    )

    val states = net.states
    val messages = net.messages
    val sms = messages.getOrElse((sender, receiver), Nil())

    val Params(n, starterProcess, ssns) = net.param

    val UID(usender) = sender
    val UID(ureceiver) = receiver

    sms match {
      case Cons(x, xs) if (x == m) =>
        val messages2 = messages.updated((sender, receiver), xs)
        0 <= usender && usender < n &&
        0 <= ureceiver && ureceiver < n &&
        intForAll2(n, n, ringChannels(n, messages)) &&
        elimForAll(n, getActorDefined(net.getActor), ureceiver) &&
        net.getActor.contains(receiver) &&
        net.getActor(receiver).myId == receiver &&
        elimForAll2(n, n, ringChannels(n, messages), usender, ureceiver) &&
        ureceiver == increment(usender, n) &&
        stillRingChannels(n, n, n, messages, usender, ureceiver, xs) &&
        elimForAll(n, smallChannel(n, messages), usender) &&
        sms.size < 2 &&
        xs.size == 0 &&
        stillSmallChannel(n, n, messages, usender, ureceiver, xs) &&
        channelsBecomeEmpty(n, n, messages, usender, ureceiver) &&
        stillOneChannel(n, n, n, messages, usender, ureceiver, xs) &&
        stillnoLeaderDuringElection(n, n, states, messages, usender, ureceiver, xs) &&
        emptyChannelsImplyElectingMax(n, n, starterProcess, messages2, net.getActor) &&
        emptyChannelsImplyElectedMax(n, n, starterProcess, messages2, net.getActor) &&
        emptyChannelsImplyElectionParticipants(n, n, starterProcess, states, messages2) &&
        intForAll(n, emptyChannel(n, messages2)) &&
        intForAll(n, statesDefined(states)) &&
        intForAll(n, getActorDefined(net.getActor)) &&
        intForAll2(n, n, ringChannels(n, messages2)) &&
        intForAll(n, smallChannel(n, messages2)) &&
        intForAll2(n, n, onlyOneChannel(n, messages2)) &&
        intForAll(n, noLeaderDuringElection(n, states, messages.updated((UID(usender), UID(ureceiver)), xs))) &&
        intForAll(n, noLeaderDuringElection(n, states, messages2)) &&
        intForAll(n, electingMax(n, starterProcess, messages2, net.getActor)) &&
        intForAll(n, electedMax(n, starterProcess, messages2, net.getActor)) &&
        intForAll(n, electionParticipants(n, starterProcess, states, messages2)) &&
        networkInvariant(net.param, states, messages2, net.getActor) &&
        (m match {
          case Election(ssn2) =>
            hasMessage(n, messages, isElectionMessage)(usender) &&
            witnessImpliesExists(n, hasMessage(n, messages, isElectionMessage), usender) &&
            existsMessage(n, messages, isElectionMessage) &&
            electionImpliesNoLeader(n, states, messages) &&
            intForAll(n, noLeader(n, states)) &&
            elimForAll(n, electingMax(n, starterProcess, messages, net.getActor), usender) && (
              ssn2 == collectMaxSSN(n, starterProcess, usender, net.getActor) ||
              ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), net.getActor)
              ) &&
            elimForAll(n, electionParticipants(n, starterProcess, states, messages), usender) &&
            forAllModulo(n, starterProcess, usender, isParticipant(n, states))

          case Elected(ssn2) =>
            elimForAll(n, electedMax(n, starterProcess, messages, net.getActor), usender) &&
            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), net.getActor)


          case _ => true
        })
      //         makeNetworkInvariant(net.param, net.states, messages2, net.getActor) &&
      case _ =>
        true
    }
  } holds


  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    val Process(UID(myuid), ssn) = a
    val Params(n, starterProcess, ssns) = net.param
    val states = net.states
    val messages = net.messages
    val getActor = net.getActor

    networkInvariant(net.param, net.states, messages, getActor) &&
    0 <= myuid && myuid < n &&
    elimForAll(n, getActorDefined(getActor), myuid) &&
    getActor(UID(myuid)) == a &&
    intForAll(n, emptyChannel(n, messages)) && (
      if (myuid == starterProcess) {
        val newMessages = messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn)))

        statesStillDefined(n, states, a.myId, Participant()) &&
        stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), List(Election(ssn))) &&
        //        intForAll2(n, n, ringChannels(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))))) &&
        //        intForAll2(n, n, ringChannels(n, newMessages)) &&
        elimForAll(n, emptyChannel(n, messages), myuid) &&
        emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), List(Election(ssn))) &&
        emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), List(Election(ssn))) &&
        intForAll(n, noLeader(n, states)) &&
        stillNoLeader(n, states, myuid, Participant()) &&
        intForAll(n, noLeader(n, states.updated(UID(myuid), Participant()))) &&
        intForAll(n, noLeader(n, states.updated(UID(myuid), Participant()))) &&
        noLeaderImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages) &&
        intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages)) &&
        ssn == collectMaxSSN(n, starterProcess, starterProcess, getActor) &&
        ssn == collectMaxSSN(n, starterProcess, myuid, getActor) &&
        stillElectingMax(n, n, starterProcess, messages, getActor, myuid, ssn) &&
        intForAll(n, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))), getActor)) &&
        newMessages == messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))) &&
        intForAll(n, electingMax(n, starterProcess, newMessages, getActor)) &&
        nothingExists(n, messages, isElectedMessage) &&
        updateChannel(n, messages, List(Election(ssn)), isElectedMessage, myuid, increment(myuid, n)) &&
        !existsMessage(n, messages.updated((UID(myuid), UID(increment(myuid,n))),List(Election(ssn))), isElectedMessage) &&
        !existsMessage(n, newMessages, isElectedMessage) &&
        states.updated(UID(myuid), Participant())(UID(starterProcess)) == Participant() &&
        forAllModulo(n, starterProcess, starterProcess, isParticipant(n, states.updated(UID(myuid), Participant()))) &&
        stillElectionParticipants(n, n, starterProcess, myuid, states.updated(UID(myuid), Participant()), messages, List(Election(ssn))) &&
        intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))))) &&
        intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), newMessages)) &&
        noElectedImpliesElectedMax(n, n, starterProcess, newMessages, getActor) &&
        intForAll(n, electedMax(n, starterProcess, newMessages, getActor)) &&
        noLeaderImpliesknowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor) &&
        intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor)) &&
        networkInvariant(net.param, states.updated(UID(myuid), Participant()), newMessages, getActor)
        //       update(Participant())
        //       !! (nextProcess, Election(ssn))
      }
      else {
        true
      })
  }

  def receivePreBranch1(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    a: Actor,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    ssns: BigInt => BigInt,
    ssn2: BigInt) = {
    require {
      val Process(UID(myuid), ssn) = a
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, getActorDefined(getActor), myuid) &&
      getActor(UID(myuid)) == a &&
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      myuid == increment(usender, n) &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      intForAll(n, noLeader(n, states)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states)) &&
      (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) ||
       ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) &&
      elimForAll(n, getActorDefined(getActor), myuid)
    }

    val Process(UID(myuid),ssn) = a
    val value = max(ssn2, ssn)
    val packet = Election(value)
    val newChannel: List[Message] = List(packet)
    val newMessages = messages.updated((UID(myuid), UID(increment(myuid, n))), newChannel)

    electionParticipantsLemma(n, starterProcess, usender, myuid, states, messages, newChannel) &&
    intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), messages.updated((UID(myuid), UID(increment(myuid, n))), newChannel))) &&
    statesStillDefined(n, states, UID(myuid), Participant()) &&
    stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), newChannel) &&
    emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), newChannel) &&
    emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), newChannel) &&
    stillNoLeader(n, states, myuid, Participant()) &&
    intForAll(n, noLeader(n, states.updated(UID(myuid), Participant()))) &&
    noLeaderImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages) &&
    intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages)) &&
    (
      if (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor)) {
        stillMax(n, starterProcess, usender, getActor) && (
          (
            max(collectMaxSSN(n, starterProcess, usender, getActor), ssn) == collectMaxSSN(n, starterProcess, increment(usender, n), getActor) &&
            value == collectMaxSSN(n, starterProcess, increment(usender, n), getActor)
            ) || (
            increment(usender, n) == starterProcess &&
            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor) &&
            maxGreater(n, starterProcess, decrement(starterProcess, n), myuid, getActor) &&
            value == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
            )
          )
      } else if (ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) {
        maxGreater(n, starterProcess, decrement(starterProcess, n), myuid, getActor) &&
        value == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
      }
      else false
      ) &&
    stillElectingMax(n, n, starterProcess, messages, getActor, myuid, value) &&
    intForAll(n, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(value))), getActor)) &&
    newMessages == messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(value))) &&
    intForAll(n, electingMax(n, starterProcess, newMessages, getActor)) &&
    nothingExists(n, messages, isElectedMessage) &&
    updateChannel(n, messages, newChannel, isElectedMessage, myuid, increment(myuid, n)) &&
    noElectedImpliesElectedMax(n, n, starterProcess, newMessages, getActor) &&
    intForAll(n, electedMax(n, starterProcess, newMessages, getActor)) &&
    noLeaderImpliesknowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor) &&
    intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor)) &&
    networkInvariant(
      Params(n, starterProcess, ssns),
      states.updated(UID(myuid), Participant()),
      messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(max(ssn2, ssn)))),
      getActor
    )
  } holds


  def receivePreBranch3(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    a: Actor,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    ssns: BigInt => BigInt,
    ssn2: BigInt) = {
    require {
      val Process(UID(myuid), ssn) = a
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, getActorDefined(getActor), myuid) &&
      getActor(UID(myuid)) == a &&
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      myuid == increment(usender, n) &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      intForAll(n, noLeader(n, states)) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states)) &&
      (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) ||
       ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) &&
      ssn2 > ssn
    }


    val Process(UID(myuid),ssn) = a
    val newChannel: List[Message] = List(Election(ssn2))
    val newMessages = messages.updated((UID(myuid), UID(increment(myuid, n))), newChannel)

    electionParticipantsLemma(n, starterProcess, usender, myuid, states, messages, newChannel) &&
    intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), messages.updated((UID(myuid), UID(increment(myuid, n))), newChannel))) &&
    stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), newChannel) &&
    emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), newChannel) &&
    emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), newChannel) &&
    intForAll(n, noLeader(n, states)) &&
    noLeaderImpliesNoLeaderDuringElection(n, states, newMessages) &&
    intForAll(n, noLeaderDuringElection(n, states, newMessages)) &&
    nothingExists(n, messages, isElectedMessage) &&
    updateChannel(n, messages, newChannel, isElectedMessage, myuid, increment(myuid, n)) &&
    noElectedImpliesElectedMax(n, n, starterProcess, newMessages, getActor) &&
    intForAll(n, electedMax(n, starterProcess, newMessages, getActor)) &&
    (
      if (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor)) {
        stillMax(n, starterProcess, usender, getActor) && (
          (
            max(collectMaxSSN(n, starterProcess, usender, getActor), ssn) == collectMaxSSN(n, starterProcess, increment(usender, n), getActor) &&
            ssn2 == collectMaxSSN(n, starterProcess, increment(usender, n), getActor)
            ) || (
            increment(usender, n) == starterProcess &&
            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
            )
          )
      } else if (ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) {
        true
      }
      else false
      ) &&
    stillElectingMax(n, n, starterProcess, messages, getActor, myuid, ssn2) &&
    intForAll(n, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))), getActor)) &&
    intForAll(n, getActorDefined(getActor)) &&
    intForAll(n, statesDefined(states)) &&
    intForAll2(n, n, ringChannels(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))))) &&
    intForAll(n, smallChannel(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))))) &&
    intForAll2(n, n, onlyOneChannel(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))))) &&
    intForAll(n, noLeaderDuringElection(n, states, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))))) &&
    intForAll2(n, n, distinctSSN(n, getActor)) &&
    intForAll(n, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))), getActor)) &&
    intForAll(n, electedMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))), getActor)) &&
    intForAll(n, electionParticipants(n, starterProcess, states, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))))) &&
    networkInvariant(
      Params(n, starterProcess, ssns),
      states,
      messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn2))),
      getActor
    )
  } holds


  def receivePreBranch4(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    a: Actor,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    ssns: BigInt => BigInt,
    ssn2: BigInt) = {
    require {
      val Process(UID(myuid), ssn) = a
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, getActorDefined(getActor), myuid) &&
      getActor(UID(myuid)) == a &&
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      myuid == increment(usender, n) &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      intForAll(n, noLeader(n, states)) &&
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      forAllModulo(n, starterProcess, usender, isParticipant(n, states)) &&
      (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) ||
       ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) &&
      elimForAll(n, getActorDefined(getActor), myuid) &&
      ssn2 == ssn
    }

    val Process(UID(myuid),ssn) = a
    val newMessages = messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2)))

    intForAll(n, statesDefined(states)) &&
    statesStillDefined(n, states, UID(myuid), KnowLeader(ssn)) &&
    intForAll(n, statesDefined(states.updated(UID(myuid), KnowLeader(ssn)))) &&
    intForAll(n, emptyChannel(n, messages)) &&
    emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    intForAll2(n, n, onlyOneChannel(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))))) &&
    emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    intForAll(n, smallChannel(n, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))))) &&
    nothingExists(n, messages, isElectionMessage) &&
    !existsMessage(n, messages, isElectionMessage) &&
    updateChannel(n, messages, List(Elected(ssn2)), isElectionMessage, myuid, increment(myuid, n)) &&
    !existsMessage(n, newMessages, isElectionMessage) &&
    noElectionImpliesElectionParticipants(n, n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn)), newMessages) &&
    noElectionImpliesElectingMax(n, n, starterProcess, newMessages, getActor) &&
    intForAll(n, electingMax(n, starterProcess, newMessages, getActor)) &&
    noElectionImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn)), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2)))) &&
    intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn)), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))))) &&
    intForAll2(n, n, ringChannels(n, messages)) &&
    stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    intForAll2(n, n, ringChannels(n, newMessages)) &&
    (
      if (ssn2 == collectMaxSSN(n, starterProcess, usender, getActor)) {
        val i = maxExists(n, starterProcess, usender, getActor)
        elimForAll(n, getActorDefined(getActor), i) && {
          val Process(_, ssn3) = getActor(UID(i))
          ssn2 == ssn3 && ssn3 == ssn &&
          elimForAll2(n, n, distinctSSN(n, getActor), i, myuid) &&
          i == myuid && inBetween(n, starterProcess, usender, i) &&
          i == increment(usender, n) &&
          increment(usender, n) == starterProcess &&
          usender == decrement(starterProcess, n) &&
          ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) &&
          ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
        }
      } else if (ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) {
        true
      }
      else false
      ) &&
    ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor) &&
    stillElectedMax(n, n, starterProcess, messages, getActor, myuid, ssn2) &&
    intForAll(n, electedMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))), getActor)) &&
    intForAll(n, electedMax(n, starterProcess, newMessages, getActor)) &&
    intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn)), newMessages)) &&
    intForAll(n, statesDefined(states.updated(UID(myuid), KnowLeader(ssn)))) &&
    stillKnowingTrueLeader(n, n, starterProcess, states, getActor, myuid, ssn2) &&
    intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn2)), getActor)) &&
    intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn)), getActor)) &&
    networkInvariant(Params(n, starterProcess, ssns), states.updated(UID(myuid), KnowLeader(ssn)), newMessages, getActor) &&
    true
  } holds


  def receivePreBranch5(
    n: BigInt,
    starterProcess: BigInt,
    usender: BigInt,
    a: Actor,
    states: MMap[ActorId, State],
    messages: MMap[(ActorId, ActorId), List[Message]],
    getActor: MMap[ActorId, Actor],
    ssns: BigInt => BigInt,
    ssn2: BigInt) = {
    require {
      val Process(UID(myuid), ssn) = a
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      0 <= myuid && myuid < n &&
      elimForAll(n, getActorDefined(getActor), myuid) &&
      getActor(UID(myuid)) == a &&
      0 <= starterProcess && starterProcess < n &&
      0 <= usender && usender < n &&
      myuid == increment(usender, n) &&
      intForAll(n, statesDefined(states)) &&
      intForAll(n, emptyChannel(n, messages)) &&
      networkInvariant(Params(n, starterProcess, ssns), states, messages, getActor) &&
      ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor) &&
      elimForAll(n, getActorDefined(getActor), myuid)
    }

    val Process(UID(myuid),ssn) = a
    val newMessages = messages.updated((UID(myuid), UID(increment(myuid,n))), List(Elected(ssn2)))

    statesStillDefined(n, states, UID(myuid), KnowLeader(ssn2)) &&
    stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), List(Elected(ssn2))) &&
    intForAll(n, emptyChannel(n, messages)) &&
    nothingExists(n, messages, isElectionMessage) &&
    !existsMessage(n, messages, isElectionMessage) &&
    updateChannel(n, messages, List(Elected(ssn2)), isElectionMessage, myuid, increment(myuid, n)) &&
    !existsMessage(n, newMessages, isElectionMessage) &&
    intForAll(n, statesDefined(states.updated(UID(myuid), KnowLeader(ssn2)))) &&
    noElectionImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn2)), newMessages) &&
    intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn2)), newMessages)) &&
    noElectionImpliesElectionParticipants(n, n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn2)), newMessages) &&
    intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn2)), newMessages)) &&
    noElectionImpliesElectingMax(n, n, starterProcess, newMessages, getActor) &&
    intForAll(n, electingMax(n, starterProcess, newMessages, getActor)) &&
    noElectionImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn2)), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2)))) &&
    intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), KnowLeader(ssn2)), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))))) &&
    stillElectedMax(n, n, starterProcess, messages, getActor, myuid, ssn2) &&
    intForAll(n, electedMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Elected(ssn2))), getActor)) &&
    intForAll(n, electedMax(n, starterProcess, newMessages, getActor)) &&
    stillKnowingTrueLeader(n, n, starterProcess, states, getActor, myuid, ssn2) &&
    intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), KnowLeader(ssn2)), getActor)) &&
    networkInvariant(Params(n, starterProcess, ssns), states.updated(UID(myuid), KnowLeader(ssn2)), newMessages, getActor) &&
    true

  } holds


  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    val Process(UID(myuid), ssn) = a
    val Params(n, starterProcess, ssns) = net.param
    val states = net.states
    val messages = net.messages
    val getActor = net.getActor
    val UID(usender) = sender

    intForAll(n, emptyChannel(n, messages)) &&
    networkInvariant(net.param, states, messages, getActor) &&
    0 <= usender && usender < n &&
    0 <= myuid && myuid < n && myuid == increment(usender,n) &&
    intForAll(n, getActorDefined(getActor)) &&
    elimForAll(n, getActorDefined(getActor), myuid) &&
    getActor(UID(myuid)) == a &&
    (m match {
      case Election(ssn2) =>
        intForAll(n, noLeader(n, states)) && (
          ssn2 == collectMaxSSN(n, starterProcess, usender, net.getActor) ||
          ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), net.getActor)
          ) &&
        forAllModulo(n, starterProcess, usender, isParticipant(n, states))
      case Elected(ssn2) =>
        ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
    }) &&
    intForAll(n, statesDefined(states)) &&
    elimForAll(n, statesDefined(states), myuid) &&
    elimForAll(n, emptyChannel(n, messages), myuid) &&
    ((sender, m, a.state) match {
      case (id, Election(ssn2), NonParticipant()) =>
        if (ssn2 != ssn) {
          //               update (Participant())
          //               !! (UID(increment(myuid,n)), Election(uid))
          receivePreBranch1(n, starterProcess, usender, a, states, messages, getActor, ssns, ssn2)
        }
        else {
          true
          //              receivePreBranch2(n, starterProcess, usender, myuid, states, messages, getActor, ssns, ssn2) &&
          //              false
          // I cannot receive an Election message equal to my uid if I'm not a participant
          //              forAllModulo(n, starterProcess, usender, isParticipant(n, states))
          //               false
        }

      case (id, Election(ssn2), Participant()) =>
        if (ssn2 > ssn) {
          //               !! (nextProcess, Election(uid))

          //          intForAll(n, statesDefined(states)) &&
          //          intForAll(n, emptyChannel(n, messages)) &&
          //          m == Election(ssn2) &&
          //          intForAll(n, noLeader(n, states)) &&
          //          forAllModulo(n, starterProcess, usender, isParticipant(n, net.states)) &&
          //          (
          //            ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) ||
          //            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) &&
          //          ssn2 > ssn &&
          receivePreBranch3(n, starterProcess, usender, a, states, messages, getActor, ssns, ssn2)

        } else if (ssn2 == ssn) {
          //               update (KnowLeader(uid))
          //               !! (nextProcess, Elected(myuid))

          receivePreBranch4(n, starterProcess, usender, a, states, messages, getActor, ssns, ssn2)

        } else {
          true
          // discard smaller uid Election message
        }

      case (id, Elected(_), NonParticipant()) =>
        // I cannot receive an Elected message if I didn't even participate yet
        true
      //             false

      case (id, Elected(ssn2), Participant()) => {
        //               update (KnowLeader(uid))
        //               !! (nextProcess, Elected(uid))
        receivePreBranch5(n, starterProcess, usender, a, states, messages, getActor, ssns, ssn2)
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

  def hasMessage(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]], p: Message => Boolean) = {
    require(n >= 0)

    (i: BigInt) =>
      0 <= i && i < n &&
      contains(messages.getOrElse((UID(i), UID(increment(i,n))), Nil()), p)
  }

  def isElectionMessage(m: Message) = {
    m match {
      case Election(_) => true
      case _ => false
    }
  }

  def isElectedMessage(m: Message) = {
    m match {
      case Elected(_) => true
      case _ => false
    }
  }

  def isKnowLeaderState(s: State) = {
    s match {
      case KnowLeader(_) => true
      case _ => false
    }
  }

  def existsMessage(n: BigInt,  messages: MMap[(ActorId,ActorId),List[Message]], p: Message => Boolean) = {
    require(n >= 0)
    intExists(n, hasMessage(n, messages, p))
  }


  def nothingExists(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]], p: Message => Boolean): Boolean = {
    require(n >= 0 && intForAll(n, emptyChannel(n, messages)))

    if (existsMessage(n, messages, p)) {
      val i = elimExists(n, hasMessage(n, messages, p))
      elimForAll(n, emptyChannel(n, messages), i) &&
      false
    }
    else
      !existsMessage(n, messages, p)
  } holds

  //   @induct
  def updateChannel(
    n: BigInt, messages: MMap[(ActorId,ActorId), List[Message]],
    tt: List[Message], p: Message => Boolean,
    usender: BigInt, ureceiver: BigInt) = {

    require(
      n >= 0 &&
      0 <= usender && usender < n &&
      ureceiver == increment(usender,n) &&
      !existsMessage(n, messages, p) &&
      !contains(tt,p)
    )

    // proof by contradiction
    if (existsMessage(n, messages.updated((UID(usender),UID(ureceiver)), tt), p)) {
      val i = elimExists(n, hasMessage(n, messages.updated((UID(usender),UID(ureceiver)), tt), p))

      if (i == usender)
        false
      else
        contains(messages.getOrElse((UID(i), UID(increment(i,n))), Nil()), p) &&
        witnessImpliesExists(n, hasMessage(n, messages, p), i) &&
        false
    }
    else
      !existsMessage(n, messages.updated((UID(usender),UID(ureceiver)), tt), p)
  } holds

  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]): Boolean = {

    validParam(p) && {
      val net = makeNetwork(p)
      val Params(n, _, _) = p
      val Process(UID(myuid), ssn) = initial_actor

      0 <= myuid && myuid < n &&
      elimForAll(n, getActorDefined(net.getActor), myuid) &&
      net.getActor(UID(myuid)) == initial_actor
    }

  }

  @extern
  def printing(s: String): Unit = println(s)

  @extern
  def printing(b: Boolean): Unit =
    if (b) println("True")
    else println("False")


  def intToString(i: BigInt): String = i.toString

  @ignore
  def main(args: Array[String]) = {
    printing(stillMax(
      2: BigInt,
      0: BigInt,
      0: BigInt,
      MMap((x: ActorId) =>
        if (x == UID(0)) Some(Process(UID(0),18))
        else Some(Process(UID(1),24))): MMap[ActorId,Actor]))
  }
}
