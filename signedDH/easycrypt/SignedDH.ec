require import AllCore FMap FSet Distr.
require import PROM.

require (*--*) St_CDH_abstract SUFCMA UATPaKE.

(** Buckle Up! **)
(* Starting notes:
   - We (try to) follow Doreen and Paul's model as closely as possible
     while remaining precise.
   - Whenever the pen and paper definition takes adversarial input in
     the form of a public key, that is then used to look for the
     identity of the intended partner, we instead takes input as
     "either a handle or a public key". This makes our definition more
     precise (because we don't make an arbitrary choice when two
     honest parties generate the same key), but also slightly more
     complex.
     In order to align with Doreen and Paul's model, we prevent the
     adversary from presenting us with a public-key that is already
     associated with a registered server. (Their definition infers
     intent; we prefer to enforce that adversary actions match
     intent.)
   - We probably want signing to be expressed as a multi-forgery game.
     (TODO: figure this out.)
   - The NIKE is split out as Nominal Group with Gap-DH + RO. The
     entire scheme could be proved assuming an abstract NIKE (with
     m-CKS-heavy security), and that be constructed from NG + Gap-DH +
     RO.
*)

(** Types and operators for the DH group **)
type pdh, sdh, sskey.

op [lossless] dkp: (pdh * sdh) distr.
op shared_key: pdh -> sdh -> pdh.

axiom shared_keyC X x Y y:
     (X, x) \in dkp
  => (Y, y) \in dkp
  => shared_key X y = shared_key Y x.

op [lossless full uniform] dssk: sskey distr.

(** Instantiate the GapDH theory **)
clone import St_CDH_abstract as StCDH with
  type pkey       <= pdh,
  type skey       <= sdh,
  op   dkp        <= dkp,
  op   shared_key <= shared_key
proof *.
realize dkp_ll by exact: dkp_ll.
realize shared_keyC by exact: shared_keyC.

(** Additional types for the signature scheme **)
type pkey, skey, sig.

(** Instantiate the UFCMA theory **)
clone import SUFCMA as Signature with
  type pkey   <= pkey,
  type skey   <= skey,
  type sig    <= sig,
  type msg    <= pdh * pdh
proof *.

(** Additional types for defining protocols,
    plus RO instantiation
**)
type client_state = { s_id: pkey;    (* The server's identity, as its public key *)
                      x_pk: pdh;     (* The client's ephemeral public key *)
                      x_sk: sdh   }. (* The client's ephemeral secret *)

clone import FullRO as H with
  type in_t    <= pdh * pdh * pdh,
  type out_t   <= sskey,
  op   dout  _ <= dssk,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

(** Instantiate the ProtRO theory **)
clone import UATPaKE as Security with
  type pkey         <= pkey,
  type skey         <= skey,
  type sskey        <= sskey,
  op   dssk         <= dssk,
  type client_state <= client_state,
  type msg1         <= pdh,
  type msg2         <= pdh * sig,
  type ro_in        <= pdh * pdh * pdh,
  type ro_out       <= sskey,
  op   d_ro         <= Self.dssk
proof *.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Finally, we define the signed DH protocol **)
module SignedDH (S : SigScheme) (H : RO) : UATPaKE = {
  proc gen() = {
    var kp;

    kp <@ S.keygen();
    return kp;
  }

  proc init(s_id) = {
    var x_pk, x_sk;

    (x_pk, x_sk) <$ dkp;
    return ({| s_id = s_id; x_pk = x_pk; x_sk = x_sk |}, x_pk);
  }

  proc resp(sk_s, x_pk) = {
    var y_pk, y_sk, s, ss, ks;

    (y_pk, y_sk) <$ dkp;
    s <@ S.sign(sk_s, (x_pk, y_pk));
    ss <- shared_key x_pk y_sk;
    ks <@ H.get(ss, x_pk, y_pk);
    return (ks, (y_pk, s));
  }

  proc recv(st, c) = {
    var y_pk, s, b, ss, kc;
    var r <- None;

    (y_pk, s) <- c;
    b <@ S.verify(s_id st, (x_pk st, y_pk), s);
    if (b) {
      ss <- shared_key y_pk (x_sk st);
      kc <@ H.get(ss, x_pk st, y_pk);
      r <- Some kc;
    }
    return r;
  }
}.

section.
declare module S <: SigScheme { -Exp_b, -RO }.
declare module A <: Adv_UATPaKE_RO { -Exp_b, -RO, -S }.

local module Game0_b = {
  (* The challenge bit *)
  var b_ror : bool

  (* Server maps: *)
  var m: int
  (* - server handle to keypair *)
  var pk_map: (int, pkey) fmap
  var sk_map: (int, skey) fmap
  (* - server-client handle to partial trace *)
  var r_map: (int option * int, (pdh * sig) fset) fmap

  (* Client maps: *)
  var n: int
  (* - client handle to state *)
  var c_map: (int, client_state) fmap
  (* - client handle to intended partner *)
  var p_map: (int, int) fmap
  (* - client handle to partial trace (early partnering) *)
  var i_map: (int, pdh) fmap

  var q   : int fset
  var ich : int fset
  var rch : int fset
  var xp  : int fset
  var cr  : int fset

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      m <- m + 1;
      (pk, sk) <@ S.keygen();
      pk_map.[m] <- pk;
      sk_map.[m] <- sk;
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c, x;

      n <- n + 1;
      (c, x) <$ dkp;
      st <- {| s_id = pk; x_pk = c; x_sk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        (h, y) <$ dkp;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(shared_key c y, c, h);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(s_id st_i, (x_pk st_i, h), sig);
          if (b) {
            k <@ RO.get(shared_key h (x_sk st_i), x_pk st_i, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h = RO.get
  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

local lemma Hop0 &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m: res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true ) @ &m: res] |
  = `|  Pr[Game0_b.run(false) @ &m: res]
      - Pr[Game0_b.run(true ) @ &m: res] |.
proof.
have ^ + -> - -> //:
  forall b, Pr[Exp_b(SignedDH(S), RO, A).run(b) @ &m: res]
          = Pr[Game0_b.run(b) @ &m: res].
move=> b; byequiv (: ={glob A, glob S, arg} ==> ={res})=> //.
proc.
(* The calls are equivalent due to equality on a bunch of variables *)
call (: ={glob S, glob RO, b_ror, m, n, q, ich, rch, xp, cr,
          c_map, p_map, i_map, r_map, pk_map, sk_map}(Exp_b, Game0_b));
  last first.
(* The invariant holds initially and allows us to conclude *)
+ by inline *; auto.
(* The invariant is preserved by all oracles *)
+ by proc; inline *; auto; call (: true); auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ proc; inline *.
  swap {1} 3 -2. swap {2} 2 -1.
  seq 1 1: (#pre /\ (x_pk, x_sk){1} = (c, x){2}).
  + by auto.
  sp 5 4. match =; 1,2:by auto.
  by move=> j; auto.
+ proc; inline *; sp; if; auto.
  swap {1} 4 -3. swap {2} 2 -1.
  swap {1} 8 -7. swap {2} 6 -5.
  seq 2 2: (#pre /\ (y_pk, y_sk){1} = (h, y){2} /\ ={r0}).
  + by auto.
  sp; seq 1 1: (#pre /\ s{1} = sig{2}).
  + by call (: true).
  sp 2 2.
  seq 1 1: #pre.
  + by auto.
  sp 3 2.
  match =; 1,2:by auto.
  by move=> i; sp; if; auto; if; auto.
+ proc; sp; if; auto; sp; if; auto.
  inline {1} 1.
  sp; seq 1 1: (#pre /\ ={b}).
  + call (: true); auto=> /> &2.
    move=> qR _ _ i_notin_qR _; exists qR=> //=.
    by exists qR.
  if; 1:by auto.
  + sp; seq 1 1: (#pre /\ kc{1} = k{2}).
    + call (: ={glob RO, arg} ==> ={glob RO, res}).
      + by sim.
      auto=> /> &2 qR _ _ i_notin_qR _ _; exists qR=> //=.
      by exists qR.
    sp; if; auto.
    by if; auto.
  rcondf {1} 2; 1:by auto.
  rcondf {2} 1; 1:by auto.
  by auto.
+ conseq (: _ ==> ={glob RO, res})=> //.
  by sim.
qed.

end section.
