
type 'a option' = 'a option =
  | None
  | Some of 'a[@@deriving yojson,show]

type 'a option = 'a option' =
  | None
  | Some of 'a[@@deriving yojson,show]

let uu___is_None = function None -> true | _ -> false
let uu___is_Some = function Some _ -> true | _ -> false
let __proj__Some__item__v = function Some x -> x | _ -> assert false

(* 'a * 'b *)
type ('a,'b) tuple2 = 'a * 'b[@@deriving yojson,show]

let fst = Pervasives.fst
let snd = Pervasives.snd

let __proj__Mktuple2__1 = fst
let __proj__Mktuple2__2 = snd

type ('a,'b,'c) tuple3 =
 'a* 'b* 'c
[@@deriving yojson,show]
let uu___is_Mktuple3 projectee = true
let __proj__Mktuple3__item___1 projectee =
  match projectee with | (_1,_2,_3) -> _1
let __proj__Mktuple3__item___2 projectee =
  match projectee with | (_1,_2,_3) -> _2
let __proj__Mktuple3__item___3 projectee =
  match projectee with | (_1,_2,_3) -> _3
type ('a,'b,'c,'d) tuple4 =
 'a* 'b* 'c* 'd
[@@deriving yojson,show]
let uu___is_Mktuple4 projectee = true
let __proj__Mktuple4__item___1 projectee =
  match projectee with | (_1,_2,_3,_4) -> _1
let __proj__Mktuple4__item___2 projectee =
  match projectee with | (_1,_2,_3,_4) -> _2
let __proj__Mktuple4__item___3 projectee =
  match projectee with | (_1,_2,_3,_4) -> _3
let __proj__Mktuple4__item___4 projectee =
  match projectee with | (_1,_2,_3,_4) -> _4
type ('a,'b,'c,'d,'e) tuple5 =
 'a* 'b* 'c* 'd* 'e
[@@deriving yojson,show]
let uu___is_Mktuple5 projectee = true
let __proj__Mktuple5__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _1
let __proj__Mktuple5__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _2
let __proj__Mktuple5__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _3
let __proj__Mktuple5__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _4
let __proj__Mktuple5__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _5
type ('a,'b,'c,'d,'e,'f) tuple6 =
 'a* 'b* 'c* 'd* 'e* 'f
[@@deriving yojson,show]
let uu___is_Mktuple6 projectee = true
let __proj__Mktuple6__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _1
let __proj__Mktuple6__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _2
let __proj__Mktuple6__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _3
let __proj__Mktuple6__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _4
let __proj__Mktuple6__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _5
let __proj__Mktuple6__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _6
type ('a,'b,'c,'d,'e,'f,'g) tuple7 =
 'a* 'b* 'c* 'd* 'e* 'f* 'g
[@@deriving yojson,show]
let uu___is_Mktuple7 projectee = true
let __proj__Mktuple7__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _1
let __proj__Mktuple7__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _2
let __proj__Mktuple7__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _3
let __proj__Mktuple7__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _4
let __proj__Mktuple7__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _5
let __proj__Mktuple7__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _6
let __proj__Mktuple7__item___7 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _7
type ('a,'b,'c,'d,'e,'f,'g,'h) tuple8 =
 'a* 'b* 'c* 'd* 'e* 'f* 'g* 'h
[@@deriving yojson,show]
let uu___is_Mktuple8 projectee = true
let __proj__Mktuple8__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _1
let __proj__Mktuple8__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _2
let __proj__Mktuple8__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _3
let __proj__Mktuple8__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _4
let __proj__Mktuple8__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _5
let __proj__Mktuple8__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _6
let __proj__Mktuple8__item___7 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _7
let __proj__Mktuple8__item___8 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _8
type ('a,'b,'c,'d,'e,'f,'g,'h,'i,'j,'k,'l,'m,'n) tuple14 =
 'a *'b *'c *'d *'e *'f *'g *'h *'i *'j *'k *'l *'m *'n
[@@deriving yojson,show]
let uu___is_Mktuple14 projectee = true
let __proj__Mktuple14__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _1
let __proj__Mktuple14__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _2
let __proj__Mktuple14__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _3
let __proj__Mktuple14__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _4
let __proj__Mktuple14__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _5
let __proj__Mktuple14__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _6
let __proj__Mktuple14__item___7 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _7
let __proj__Mktuple14__item___8 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _8
let __proj__Mktuple14__item___9 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _9
let __proj__Mktuple14__item___10 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _10
let __proj__Mktuple14__item___11 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _11
let __proj__Mktuple14__item___12 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _12
let __proj__Mktuple14__item___13 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _13
let __proj__Mktuple14__item___14 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14) -> _14


type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | Reify
    | NBE
    | UnfoldOnly  : string list -> norm_step
    | UnfoldFully : string list -> norm_step
    | UnfoldAttr  : string list -> norm_step

let simplify : norm_step = Simpl
let weak    : norm_step = Weak
let hnf     : norm_step = HNF
let primops : norm_step = Primops
let delta   : norm_step = Delta
let zeta    : norm_step = Zeta
let iota    : norm_step = Iota
let delta_only  (s : string list) : norm_step = UnfoldOnly  s
let delta_fully (s : string list) : norm_step = UnfoldFully s
let delta_attr  (s : string list) : norm_step = UnfoldAttr  s
let reify   : norm_step = Reify
let nbe     : norm_step = NBE

let singleton x = x
