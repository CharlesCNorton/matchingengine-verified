(******************************************************************************)
(*                                                                            *)
(*            Matching Engine: Exchange Order Book Price-Time Priority        *)
(*                                                                            *)
(*     Formal verification of continuous double auction matching rules.       *)
(*     Encodes price-time priority, order types, fill-or-kill semantics,      *)
(*     and crossed book resolution.                                           *)
(*                                                                            *)
(*     "The stock exchange is a poor substitute for the Holy Grail."          *)
(*     - John Maynard Keynes, 1936                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

