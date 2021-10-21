(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Simplified model of x86 semantics.                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Size in bits corresponding to the tags.                                   *)
(* ------------------------------------------------------------------------- *)

let bytesize = define
 `bytesize Byte = 8 /\
  bytesize Word = 16 /\
  bytesize Doubleword = 32 /\
  bytesize Quadword = 64`;;

let regsize = define
 `regsize Full_64 = 64 /\
  regsize Lower_32 = 32 /\
  regsize Lower_16 = 16 /\
  regsize Upper_8 = 8 /\
  regsize Lower_8 = 8`;;

let simdregsize = define
 `simdregsize Full_512 = 512 /\
  simdregsize Lower_256 = 256 /\
  simdregsize Lower_128 = 128`;;

let register_size = define
 `register_size (Gpr n w) = regsize w`;;

let simdregister_size = define
 `simdregister_size (Simdreg n w) = simdregsize w`;;

let operand_size = define
 `operand_size (Register r) = register_size r /\
  operand_size (Simdregister s) = simdregister_size s /\
  operand_size (Imm8 i8) = 8 /\
  operand_size (Imm16 i16) = 16 /\
  operand_size (Imm32 i32) = 32 /\
  operand_size (Imm64 i64) = 64 /\
  operand_size (Memop w b) = bytesize w`;;

(* ------------------------------------------------------------------------- *)
(* The semantics.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** Note: we currently treat memory as a full 64-bit address space.
 *** In current processors, especially AMD, there are some canonicality
 *** assumptions (address must be sign-extended 48 bit value, i.e. the
 *** top 16 bits must be all 0s or all 1s). We can add those later when
 *** considering general memory protection properly.
 ***)

let x86state_INDUCT,x86state_RECURSION,x86state_COMPONENTS =
  define_auto_record_type
   "x86state =
     { RIP : int64;                       // instruction pointer (RIP)
       registers : (4)word -> (64)word;   // 2^4=16 GP registers, 64 bits each
       simdregisters: (5)word->(512)word; // 2^5=32 ZMM registers, 512 bits each
       maskregisters: (3)word->(64)word;  // 2^3=8 opmasks, can be up to 64-bit
       rflags : int64;                    // rflags register (top 32 reserved)
       memory : int64 -> byte             // Memory
     }";;

let FORALL_X86STATE = prove
 (`!P. (!i r z k f m. P(x86state_RECORD i r z k f m)) <=> (!s. P s)`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[x86state_INDUCT]);;

let bytes_loaded = new_definition
 `bytes_loaded s pc l <=>
     read (memory :> bytelist(pc,LENGTH l)) s = l`;;

let bytes_loaded_nil = prove (`bytes_loaded s pc []`, REWRITE_TAC [
  bytes_loaded; READ_COMPONENT_COMPOSE; LENGTH; bytelist_clauses]);;

let bytes_loaded_append = prove
 (`bytes_loaded s pc (APPEND l1 l2) <=>
   bytes_loaded s pc l1 /\ bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC [bytes_loaded; READ_COMPONENT_COMPOSE; read_bytelist_append]);;

let bytes_loaded_unique = METIS [bytes_loaded]
 `!s pc l1 l2. bytes_loaded s pc l1 ==> bytes_loaded s pc l2 ==>
  LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let bytes_loaded_update = METIS [bytes_loaded]
 `!l n. LENGTH l = n ==> !s pc. bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' = read(memory :> bytelist(pc,n)) s ==>
    bytes_loaded s' pc l`;;

let bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==>
   !s pc. bytes_loaded s (word pc) l ==>
          bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REWRITE_TAC [WORD_ADD] THEN METIS_TAC [bytes_loaded_append]);;

(* ------------------------------------------------------------------------- *)
(* Shorthands for individual flags.                                          *)
(* ------------------------------------------------------------------------- *)

(*** Note: this does not build in the conception that some bits
 *** (e.g. 1) are "reserved" and always 0 or 1. That could be added
 *** to the semantics of any instructions operating on the flags register.
 ***)

let CF = define `CF = rflags :> bitelement 0`;;

let PF = define `PF = rflags :> bitelement 2`;;

let AF = define `AF = rflags :> bitelement 4`;;

let ZF = define `ZF = rflags :> bitelement 6`;;

let SF = define `SF = rflags :> bitelement 7`;;

let OF = define `OF = rflags :> bitelement 11`;;

add_component_alias_thms [CF; PF; AF; ZF; SF; OF];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the general-purpose registers.                             *)
(* ------------------------------------------------------------------------- *)

let RAX = define `RAX = registers :> element (word  0)`
and RCX = define `RCX = registers :> element (word  1)`
and RDX = define `RDX = registers :> element (word  2)`
and RBX = define `RBX = registers :> element (word  3)`
and RSP = define `RSP = registers :> element (word  4)`
and RBP = define `RBP = registers :> element (word  5)`
and RSI = define `RSI = registers :> element (word  6)`
and RDI = define `RDI = registers :> element (word  7)`
and  R8 = define ` R8 = registers :> element (word  8)`
and  R9 = define ` R9 = registers :> element (word  9)`
and R10 = define `R10 = registers :> element (word 10)`
and R11 = define `R11 = registers :> element (word 11)`
and R12 = define `R12 = registers :> element (word 12)`
and R13 = define `R13 = registers :> element (word 13)`
and R14 = define `R14 = registers :> element (word 14)`
and R15 = define `R15 = registers :> element (word 15)`;;

add_component_alias_thms
 [RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI;
   R8;  R9; R10; R11; R12; R13; R14; R15];;

let  EAX = define ` EAX = RAX :> bottom_32`
and  ECX = define ` ECX = RCX :> bottom_32`
and  EDX = define ` EDX = RDX :> bottom_32`
and  EBX = define ` EBX = RBX :> bottom_32`
and  ESP = define ` ESP = RSP :> bottom_32`
and  EBP = define ` EBP = RBP :> bottom_32`
and  ESI = define ` ESI = RSI :> bottom_32`
and  EDI = define ` EDI = RDI :> bottom_32`
and  R8D = define ` R8D =  R8 :> bottom_32`
and  R9D = define ` R9D =  R9 :> bottom_32`
and R10D = define `R10D = R10 :> bottom_32`
and R11D = define `R11D = R11 :> bottom_32`
and R12D = define `R12D = R12 :> bottom_32`
and R13D = define `R13D = R13 :> bottom_32`
and R14D = define `R14D = R14 :> bottom_32`
and R15D = define `R15D = R15 :> bottom_32`;;

add_component_alias_thms
  [ EAX;  ECX;  EDX;  EBX;  ESP;  EBP;  ESI;  EDI;
    R8D;  R9D; R10D; R11D; R12D; R13D; R14D; R15D];;

let AX = define `AX = EAX :> bottom_16`
and CX = define `CX = ECX :> bottom_16`
and DX = define `DX = EDX :> bottom_16`
and BX = define `BX = EBX :> bottom_16`
and SP = define `SP = ESP :> bottom_16`
and BP = define `BP = EBP :> bottom_16`
and SI = define `SI = ESI :> bottom_16`
and DI = define `DI = EDI :> bottom_16`;;

add_component_alias_thms [AX; CX; DX; BX; SP; BP; SI; DI];;

let AH = define `AH = AX :> top_8`;;
let AL = define `AL = AX :> bottom_8`;;
let BH = define `BH = BX :> top_8`;;
let BL = define `BL = BX :> bottom_8`;;
let CH = define `CH = CX :> top_8`;;
let CL = define `CL = CX :> bottom_8`;;
let DH = define `DH = DX :> top_8`;;
let DL = define `DL = DX :> bottom_8`;;

add_component_alias_thms [AH; AL; BH; BL; CH; CL; DH; DL];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the SIMD registers.                                        *)
(* ------------------------------------------------------------------------- *)

let ZMM0  = define `ZMM0  = simdregisters :> element(word 0)`
and ZMM1  = define `ZMM1  = simdregisters :> element(word 1)`
and ZMM2  = define `ZMM2  = simdregisters :> element(word 2)`
and ZMM3  = define `ZMM3  = simdregisters :> element(word 3)`
and ZMM4  = define `ZMM4  = simdregisters :> element(word 4)`
and ZMM5  = define `ZMM5  = simdregisters :> element(word 5)`
and ZMM6  = define `ZMM6  = simdregisters :> element(word 6)`
and ZMM7  = define `ZMM7  = simdregisters :> element(word 7)`
and ZMM8  = define `ZMM8  = simdregisters :> element(word 8)`
and ZMM9  = define `ZMM9  = simdregisters :> element(word 9)`
and ZMM10 = define `ZMM10 = simdregisters :> element(word 10)`
and ZMM11 = define `ZMM11 = simdregisters :> element(word 11)`
and ZMM12 = define `ZMM12 = simdregisters :> element(word 12)`
and ZMM13 = define `ZMM13 = simdregisters :> element(word 13)`
and ZMM14 = define `ZMM14 = simdregisters :> element(word 14)`
and ZMM15 = define `ZMM15 = simdregisters :> element(word 15)`
and ZMM16 = define `ZMM16 = simdregisters :> element(word 16)`
and ZMM17 = define `ZMM17 = simdregisters :> element(word 17)`
and ZMM18 = define `ZMM18 = simdregisters :> element(word 18)`
and ZMM19 = define `ZMM19 = simdregisters :> element(word 19)`
and ZMM20 = define `ZMM20 = simdregisters :> element(word 20)`
and ZMM21 = define `ZMM21 = simdregisters :> element(word 21)`
and ZMM22 = define `ZMM22 = simdregisters :> element(word 22)`
and ZMM23 = define `ZMM23 = simdregisters :> element(word 23)`
and ZMM24 = define `ZMM24 = simdregisters :> element(word 24)`
and ZMM25 = define `ZMM25 = simdregisters :> element(word 25)`
and ZMM26 = define `ZMM26 = simdregisters :> element(word 26)`
and ZMM27 = define `ZMM27 = simdregisters :> element(word 27)`
and ZMM28 = define `ZMM28 = simdregisters :> element(word 28)`
and ZMM29 = define `ZMM29 = simdregisters :> element(word 29)`
and ZMM30 = define `ZMM30 = simdregisters :> element(word 30)`
and ZMM31 = define `ZMM31 = simdregisters :> element(word 31)`;;

add_component_alias_thms
 [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
  ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15;
  ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
  ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31];;

let YMM0  = define `YMM0  = ZMM0  :> bottom_256`
and YMM1  = define `YMM1  = ZMM1  :> bottom_256`
and YMM2  = define `YMM2  = ZMM2  :> bottom_256`
and YMM3  = define `YMM3  = ZMM3  :> bottom_256`
and YMM4  = define `YMM4  = ZMM4  :> bottom_256`
and YMM5  = define `YMM5  = ZMM5  :> bottom_256`
and YMM6  = define `YMM6  = ZMM6  :> bottom_256`
and YMM7  = define `YMM7  = ZMM7  :> bottom_256`
and YMM8  = define `YMM8  = ZMM8  :> bottom_256`
and YMM9  = define `YMM9  = ZMM9  :> bottom_256`
and YMM10 = define `YMM10 = ZMM10 :> bottom_256`
and YMM11 = define `YMM11 = ZMM11 :> bottom_256`
and YMM12 = define `YMM12 = ZMM12 :> bottom_256`
and YMM13 = define `YMM13 = ZMM13 :> bottom_256`
and YMM14 = define `YMM14 = ZMM14 :> bottom_256`
and YMM15 = define `YMM15 = ZMM15 :> bottom_256`;;

add_component_alias_thms
 [YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7;
  YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15];;

let XMM0  = define `XMM0  = YMM0  :> bottom_128`
and XMM1  = define `XMM1  = YMM1  :> bottom_128`
and XMM2  = define `XMM2  = YMM2  :> bottom_128`
and XMM3  = define `XMM3  = YMM3  :> bottom_128`
and XMM4  = define `XMM4  = YMM4  :> bottom_128`
and XMM5  = define `XMM5  = YMM5  :> bottom_128`
and XMM6  = define `XMM6  = YMM6  :> bottom_128`
and XMM7  = define `XMM7  = YMM7  :> bottom_128`
and XMM8  = define `XMM8  = YMM8  :> bottom_128`
and XMM9  = define `XMM9  = YMM9  :> bottom_128`
and XMM10 = define `XMM10 = YMM10 :> bottom_128`
and XMM11 = define `XMM11 = YMM11 :> bottom_128`
and XMM12 = define `XMM12 = YMM12 :> bottom_128`
and XMM13 = define `XMM13 = YMM13 :> bottom_128`
and XMM14 = define `XMM14 = YMM14 :> bottom_128`
and XMM15 = define `XMM15 = YMM15 :> bottom_128`;;

add_component_alias_thms
 [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
  XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15];;

(*** Note that K0 is actually hardwired to all-1s              ***)
(*** So strictly we should have left it out of the state above ***)

let K0 = define `K0:(x86state,(64)word)component = rvalue(word_not(word 0))`;;
let K1 = define `K1 = maskregisters :> element(word 1)`;;
let K2 = define `K2 = maskregisters :> element(word 2)`;;
let K3 = define `K3 = maskregisters :> element(word 3)`;;
let K4 = define `K4 = maskregisters :> element(word 4)`;;
let K5 = define `K5 = maskregisters :> element(word 5)`;;
let K6 = define `K6 = maskregisters :> element(word 6)`;;
let K7 = define `K7 = maskregisters :> element(word 7)`;;

(* ------------------------------------------------------------------------- *)
(* Semantics of conditions.                                                  *)
(* ------------------------------------------------------------------------- *)

let condition_semantics = define
 `(condition_semantics Unconditional s <=>
        T) /\
  (condition_semantics Condition_B s <=>
        read CF s) /\
  (condition_semantics Condition_BE s <=>
        read CF s \/ read ZF s) /\
  (condition_semantics Condition_L s <=>
        ~(read SF s <=> read OF s)) /\
  (condition_semantics Condition_LE s <=>
        ~(read SF s <=> read OF s) \/ read ZF s) /\
  (condition_semantics Condition_NB s <=>
        ~read CF s) /\
  (condition_semantics Condition_NBE s <=>
        ~(read CF s \/ read ZF s)) /\
  (condition_semantics Condition_NL s <=>
        (read SF s <=> read OF s)) /\
  (condition_semantics Condition_NLE s <=>
        (read SF s <=> read OF s) /\ ~read ZF s) /\
  (condition_semantics Condition_NO s <=>
        ~read OF s) /\
  (condition_semantics Condition_NP s <=>
        ~read PF s) /\
  (condition_semantics Condition_NS s <=>
        ~read SF s) /\
  (condition_semantics Condition_NZ s <=>
        ~read ZF s) /\
  (condition_semantics Condition_O s <=>
        read OF s) /\
  (condition_semantics Condition_P s <=>
        read PF s) /\
  (condition_semantics Condition_S s <=>
        read SF s) /\
  (condition_semantics Condition_Z s <=>
        read ZF s)`;;

(* ------------------------------------------------------------------------- *)
(* Exceptions. Currently the semantics is basically "some arbitrary state".  *)
(* But we distinguish things so this can become a more accurate model later. *)
(* In general there is also a 64-bit data field with some exceptions         *)
(* ------------------------------------------------------------------------- *)

let raise_exception = new_definition
 `raise_exception (b:byte) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let raise_exception_with = new_definition
 `raise_exception_with (b:byte) (d:int64) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let x86_Exception_DE = new_definition
  `x86_Exception_DE = (word 0x00 :byte)`;;

let x86_Exception_DB = new_definition
  `x86_Exception_DB = (word 0x01 :byte)`;;

let x86_Exception_NMI = new_definition
  `x86_Exception_NMI = (word 0x02 :byte)`;;

let x86_Exception_BP = new_definition
  `x86_Exception_BP = (word 0x03:byte)`;;

let x86_Exception_OF = new_definition
  `x86_Exception_OF = (word 0x04 :byte)`;;

let x86_Exception_BR = new_definition
  `x86_Exception_BR = (word 0x05 :byte)`;;

let x86_Exception_UD = new_definition
  `x86_Exception_UD = (word 0x06 :byte)`;;

let x86_Exception_NM = new_definition
  `x86_Exception_NM = (word 0x07 :byte)`;;

let x86_Exception_DF = new_definition
  `x86_Exception_DF = (word 0x08 :byte)`;;

let x86_Exception_TS = new_definition
  `x86_Exception_TS = (word 0x0A :byte)`;;

let x86_Exception_NP = new_definition
  `x86_Exception_NP = (word 0x0B :byte)`;;

let x86_Exception_SS = new_definition
  `x86_Exception_SS = (word 0x0C :byte)`;;

let x86_Exception_GP = new_definition
  `x86_Exception_GP = (word 0x0D :byte)`;;

let x86_Exception_PF = new_definition
  `x86_Exception_PF = (word 0x0E :byte)`;;

let x86_Exception_MF = new_definition
  `x86_Exception_MF = (word 0x10 :byte)`;;

let x86_Exception_AC = new_definition
  `x86_Exception_AC = (word 0x11 :byte)`;;

let x86_Exception_MC = new_definition
  `x86_Exception_MC = (word 0x12 :byte)`;;

let x86_Exception_XF = new_definition
  `x86_Exception_XF = (word 0x13 :byte)`;;

let x86_Exception_VE = new_definition
  `x86_Exception_VE = (word 0x14 :byte)`;;

let x86_Exception_SX = new_definition
  `x86_Exception_SX = (word 0x1E :byte)`;;

(* ------------------------------------------------------------------------- *)
(* The core operations with generic sizes, to be instantiated to any of      *)
(* 8, 16, 32 or 64. In effect this is a kind of shallow embedding of x86.    *)
(* ------------------------------------------------------------------------- *)

let x86_ADC = new_definition
 `x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y + c = val z) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`;;

let x86_ADCX = new_definition
 `x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         CF := ~(val x + val y + c = val z)) s`;;

let x86_ADD = new_definition
 `x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y = val z) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`;;

let x86_ADOX = new_definition
 `x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         OF := ~(val x + val y + c = val z)) s`;;

let x86_AND = new_definition
 `x86_AND dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(*** These are similar to TZCNT and (less so, dual) LZCNT. Besides one
 *** being dualized, they are officially undefined on zero inputs.
 *** The flag settings are also different: the input determines ZF and
 *** the others are undefined (on TZCNT/LZCNT the output determines ZF).
 *** They have the merit of being pure x86-64 and not needing even
 *** moderately recent extensions.
 ***)

let x86_BSF = new_definition
 `x86_BSF dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSR = new_definition
 `x86_BSR dest src s =
        let x:N word = read src s in
        let z:N word = word(dimindex(:N) - 1 - word_clz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSWAP = new_definition
 `x86_BSWAP dest s =
        let x:N word = read dest s in
        let x' = word_of_bits
                   (\i. bit (dimindex(:N) - 8 * (i DIV 8 + 1) + i MOD 8) x) in
        (dest := x') s`;;

(*** These four amount to the core operations for BT, BTC, BTR and BTS.
 *** When the first operand is a register this is the entire thing.
 *** With memory operands however, the upper part is used to offset the
 *** address (presumably DIV means Euclidean division?) and sometimes
 *** assemblers even support that kind of thing for immediates. So the
 *** dispatch needs to treat different operands differently, unless we
 *** choose to define some more generic "bit" of a state components.
 ***)

let x86_BT = new_definition
 `x86_BT dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTC = new_definition
 `x86_BTC dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := ~b ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTR = new_definition
 `x86_BTR dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := F ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTS = new_definition
 `x86_BTS dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := T ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_CLC = new_definition
 `x86_CLC s =
        (CF := F) s`;;

let x86_CMC = new_definition
 `x86_CMC s =
        let c = read CF s in
        (CF := ~c) s`;;

let x86_CMOV = new_definition
 `x86_CMOV cc dest src s =
        (dest := (if condition_semantics cc s then read src s
                  else read dest s)) s`;;

let x86_CMP = new_definition
 `x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:N word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_DEC = new_definition
 `x86_DEC dest s =
        let x = read dest s in
        let z = word_sub x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x - &1 = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &1:int =
                 &(val(word_zx z:nybble)))) s`;;

(*** Again we make the operands explicit in this function. In the
 *** final dispatch most of the sources and destinations are implicit
 *** and drawn from RAX / RDX and its shorter versions
 ***)

let x86_DIV2 = new_definition
 `x86_DIV2 (dest_quo,dest_rem) (src_hi,src_lo) divisor s =
        let x = 2 EXP dimindex(:N) * val(read src_hi s:N word) +
                val(read src_lo s:N word)
        and y = val(read divisor s:N word) in
        if y = 0 then
          raise_exception x86_Exception_DE s
        else
          let q = x DIV y and r = x MOD y in
          if 2 EXP dimindex(:N) <= q then
            raise_exception x86_Exception_DE s
          else
           (dest_quo := (word q:N word) ,,
            dest_rem := (word r:N word) ,,
            UNDEFINED_VALUES [CF;ZF;ZF; PF;OF;ZF]) s`;;

(*** There are really four different multiplies here.
 ***
 *** 1. x86_IMUL: a signed multiply with the same length for operands
 ***    and result, corresponding to the "two operand" and "three operand"
 ***    forms in the manual, with three operands to allow flexibility at this
 ***    level. Note that as usual the result is signed/unsigned-agnostic in
 ***    this setting. But the overflow and carry settings are *both* signed.

 *** 2. x86_IMUL2: A signed two-part multiply, corresponding to the
 ***    "one-operand form" in the manuals. The carry and overflow seem to
 ***    be set in the same way and as one would expect, according to recent
 ***    documentation and a few experiments. However much older manuals say
 ***    something different. (Whether the top is something other than all
 ***    0s or all 1s --- implying for example 2^31 * 2^32 would not set it.)

 *** 3. x86_MUL2: An unsigned two-part signed multiply. The detection of
 ***    CF=OF is based on whether the top is nonzero. The code for this is
 ***    further below following alphabetical order.

 *** 4. x86_MULX4: An unsigned 2-part multiply without affecting flags. In
 ***    the final dispatch the first source is explicit (edx/rdx). Note that
 ***    it's important to assign the high part *second* to match the ISA
 ***    manual "if the first and second operands are identical, it will contain
 ***    the high half of the multiplication results". In others we happen to
 ***    do it the other way round, but maybe for uniformity should change that.
 ***)

let x86_IMUL3 = new_definition
 `x86_IMUL3 dest (src1,src2) s =
        let x = read src1 s and y = read src2 s in
        let z = word_mul x y in
        (dest := (z:N word) ,,
         CF := ~(ival x * ival y = ival z) ,,
         OF := ~(ival x * ival y = ival z) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_IMUL = new_definition
 `x86_IMUL dest src = x86_IMUL3 dest (dest,src)`;;

let x86_IMUL2 = new_definition
 `x86_IMUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = iword(ival x * ival y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(ival x * ival y = ival z_lo) ,,
         OF := ~(ival x * ival y = ival z_lo) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_INC = new_definition
 `x86_INC dest s =
        let x = read dest s in
        let z = word_add x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x + &1 = ival z) ,,
         AF := ~(val(word_zx x:nybble) + 1 =
                 val(word_zx z:nybble))) s`;;

(*** At this level this is trivial: the EA is from operand decoding ***)

let x86_LEA = new_definition
 `x86_LEA dest ea s =
        (dest := ea) s`;;

let x86_LZCNT = new_definition
 `x86_LZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_clz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_MOV = new_definition
 `x86_MOV dest src s =
        let x = read src s in (dest := x) s`;;

(*** These are rare cases with distinct operand sizes
 ***
 *** A bit bizarrely there are same-size versions of MOVSXD (not MOVZXD)
 *** But these seem to be just freaks of decoding so we ignore them.
 *** The documentation says "regular MOV should be used" instead.
 *** But we do have a real 32-bit to 64-bit version of MOVSX(D), whereas
 *** the equivalent MOVZX is just done by the usual MOV in 64-bit mode.
 ***)

let x86_MOVSX = new_definition
 `x86_MOVSX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_sx x in
        (dest := x') s`;;

let x86_MOVZX = new_definition
 `x86_MOVZX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_zx x in
        (dest := x') s`;;

(*** See comments above for IMUL. No other version of unsigned mul ***)

let x86_MULX4 = new_definition
 `x86_MULX4 (dest_hi,dest_lo) (src1,src2) s =
        let (x:N word) = read src1 s and (y:N word) = read src2 s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_lo := z_lo ,,
         dest_hi := z_hi) s`;;

let x86_MUL2 = new_definition
 `x86_MUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(z_hi = word 0) ,,
         OF := ~(z_hi = word 0) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

(*** Note that the Intel documentation states the CF setting very explicitly
 *** as "the source operand is nonzero". So I copy that here. But it is just
 *** the same as the uniform value you'd get from 0 - x

  WORD_ARITH
   `&(val(word_sub x y)):int = &(val x) - &(val y) <=> val y <= val x`;;

  WORD_ARITH
    `-- (&(val x)):int = &(val(word_neg x)) <=> x = word 0`;;

 ***)

let x86_NEG = new_definition
 `x86_NEG dest s =
        let x = read dest s in
        let z = word_neg x in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(x = word 0) ,,
         OF := ~(-- ival x = ival z) ,,
         AF := ~(-- &(val(word_zx x:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_NOP = new_definition
 `x86_NOP (s:x86state) = \s'. s = s'`;;

(*** In contrast to most logical ops, NOT doesn't affect any flags ***)

let x86_NOT = new_definition
 `x86_NOT dest s =
        let x = read dest s in
        let z = word_not x in
        (dest := (z:N word)) s`;;

let x86_OR = new_definition
 `x86_OR dest src s =
        let x = read dest s and y = read src s in
        let z = word_or x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(*** Push and pop are a bit odd in several ways. First of all, there is  ***)
(*** an implicit memory operand so this doesn't have quite the same      ***)
(*** "shallowness": we refer to the memory component explicitly. And we  ***)
(*** need to adjust the sizes dynamically and hence use x:num inside.    ***)
(*** Note that in 64-bit mode you can only have sizes 16 or 64 so the    ***)
(*** full genericity of this function is not used in our setting.        ***)
(*** Finally, we ignore all the versions with segment registers.         ***)
(*** The handling of pushing and popping RSP itself is an obvious corner ***)
(*** case in which the documentation is poor, and completely different   ***)
(*** (at least in style if not intended meaning) in the Intel and AMD    ***)
(*** manuals. Nevertheless I believe the treatment here is right.        ***)

let x86_POP = new_definition
 `x86_POP dest s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s in
        let x:N word = word(read (memory :> bytes(p,n)) s) in
        let p' = word_add p (word n) in
        (RSP := p' ,,
         dest := x) s`;;

let x86_PUSH = new_definition
 `x86_PUSH src s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s
        and x = val(read src s:N word) in
        let p' = word_sub p (word n) in
        (RSP := p' ,,
         memory :> bytes(p',n) := x) s`;;

(*** Out of alphabetical order as PUSH is a subroutine ***)

let x86_CALL = new_definition
 `x86_CALL target =
    x86_PUSH RIP ,, RIP := target`;;

(*** We don't distinguish near/far and don't have the form with the ***)
(*** additional "release more bytes" argument, so it's quite simple ***)

let x86_RET = new_definition
 `x86_RET s =
        let p = read RSP s in
        let p' = word_add p (word 8)
        and ip' = read (memory :> bytes64 p) s in
        (RSP := p' ,, RIP := ip') s`;;

(*** Shift and rotate operations mask to 5 bits, or 6 bits in 64-bit     ***)
(*** Actually it's even more complicated for RCL and RCR in general:     ***)
(*** for sizes 8 and 16 they go mod 9 and 17 (natural enough) but then   ***)
(*** 32-bit and 64-bit forms just mask as in the others. Not generic.    ***)

(*** It's not quite enough to just use the native size, as certain       ***)
(*** things are different in case case masked_shift IN {0,1} (e.g. OF)   ***)
(*** We assume that the masked value comes in from the decoder           ***)
(*** Our underlying rotate functions are modulo anyway.                  ***)
(*** It is at least clearly stated that SF, ZF, AF, PF are unaffected    ***)
(*** It's also stated that no flags are affected for zero masked count   ***)
(*** The manual is confusing about "affected" versus "defined" on the    ***)
(*** OF result for counts > 1.                                           ***)

(*** Note that in the unpacking of the actual instructions below we can  ***)
(*** assume the shift is an 8-bit operand (an immediate or CL, in fact   ***)
(*** in the actual encodings.)                                           ***)

(*** Note that RCL and RCR don't special case the zero for CF, since     ***)
(*** it will anyway be the input CF in that case                         ***)

(*** The OF definitions are confusing but I hope correct.                ***)

let x86_RCL = new_definition
 `x86_RCL dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_rol xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
               OF := read OF s
          else if c = 1 then
               OF := ~(bit (dimindex(:N)-1) z = cout)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_RCR = new_definition
 `x86_RCR dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_ror xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROL = new_definition
 `x86_ROL dest c s =
        let x = read dest s in
        let z = word_rol x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit 0 z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit 0 z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROR = new_definition
 `x86_ROR dest c s =
        let x = read dest s in
        let z = word_ror x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit (dimindex(:N)-1) z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

(*** Note that SAL and SHL are the same thing ***)

let x86_SAR = new_definition
 `x86_SAR dest c s =
      let x = read dest s in
      let z = word_ishr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ishr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := F
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SBB = new_definition
 `x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - (&(val y) + &c):int = &(val z)) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`;;

(*** Note: SET is only ever applied to 8-bit operands, so we build
 *** this into the type, in contrast to most of the other cases where
 *** this is generic
 ***)

let x86_SET = new_definition
 `x86_SET cc dest s =
          (dest := (if condition_semantics cc s then
                    word 1:byte else word 0)) s`;;

let x86_SHL = new_definition
 `x86_SHL dest c s =
      let x = read dest s in
      let z = word_shl x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s
              else bit (dimindex(:N)-1) (word_shl x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) x = bit (dimindex(:N)-2) x)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHLD = new_definition
 `x86_SHLD dest src c s =
      let h:N word = read dest s
      and l:N word = read src s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (64 - c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (64 - c) h) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) h)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHR = new_definition
 `x86_SHR dest c s =
      let x = read dest s in
      let z = word_ushr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ushr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := bit (dimindex(:N)-1) x
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHRD = new_definition
 `x86_SHRD dest src c s =
      let h:N word = read src s
      and l:N word = read dest s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (c - 1) l) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) l)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_STC = new_definition
 `x86_STC s =
        (CF := T) s`;;

let x86_SUB = new_definition
 `x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

(*** This is roughly AND just for some condition codes ***)

let x86_TEST = new_definition
 `x86_TEST dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

let x86_TZCNT = new_definition
 `x86_TZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_XOR = new_definition
 `x86_XOR dest src s =
        let x = read dest s and y = read src s in
        let z = word_xor x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(* ------------------------------------------------------------------------- *)
(* State components of various sizes corresponding to GPRs.                  *)
(* We also have a generic one "GPR" mapping to a number in all cases.        *)
(* ------------------------------------------------------------------------- *)

let GPR8 = define
 `GPR8 (Gpr reg Upper_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> top_8  /\
  GPR8 (Gpr reg Lower_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> bottom_8 `;;

let GPR16 = define
 `GPR16 (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16`;;

let GPR32 = define
 `GPR32 (Gpr reg Lower_32) = registers :> element reg :> bottom_32`;;

(*** This is the behavior in 64-bit mode. ***)

let GPR32_Z = define
 `GPR32_Z (Gpr reg Lower_32) = registers :> element reg :> zerotop_32`;;

let GPR64 = define
 `GPR64 (Gpr reg Full_64) = registers :> element reg`;;

let GPR = define
  `GPR (Gpr reg Full_64) =
        registers :> element reg :> asnumber /\
   GPR (Gpr reg Lower_32) =
        registers :> element reg :> bottom_32 :> asnumber /\
   GPR (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16 :> asnumber /\
   GPR (Gpr reg Upper_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> top_8 :> asnumber /\
   GPR (Gpr reg Lower_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> bottom_8 :> asnumber`;;

(* ------------------------------------------------------------------------- *)
(* Decoding of a bsid address, always returning a 64-bit word.               *)
(* ------------------------------------------------------------------------- *)

let bsid_semantics = define
 `bsid_semantics(Bsid obase oind scl disp) s =
        let bv = match obase with SOME base -> read (GPR base) s | NONE -> 0
        and iv = match oind with SOME ind -> read (GPR ind) s | NONE -> 0 in
        word(bv + 2 EXP (val scl) * iv + val disp):64 word`;;

(* ------------------------------------------------------------------------- *)
(* Translate an operand to a state component of given size.                  *)
(* Generally, the only "type casts" we want are for immediates,              *)
(* which are always sign-extended. Leave other things undefined.             *)
(* Note: this is in 64-bit mode only. Of course things are different in      *)
(* other modes; particularly the "zerotop" stuff does not apply then.        *)
(* ------------------------------------------------------------------------- *)

let OPERAND64 = define
 `OPERAND64 (Register r) s =
        (if register_size r = 64 then GPR64 r else ARB) /\
  OPERAND64 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND64 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND64 (Imm32 imm32) s = rvalue(word_sx imm32) /\
  OPERAND64 (Imm64 imm64) s = rvalue imm64 /\
  OPERAND64 (Memop w ea) s =
       (if w = Quadword then memory :> bytes64 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND32 = define
 `OPERAND32 (Register r) s =
        (if register_size r = 32 then GPR32_Z r else ARB) /\
  OPERAND32 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND32 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND32 (Imm32 imm32) s = rvalue imm32 /\
  OPERAND32 (Memop w ea) s =
       (if w = Doubleword then memory :> bytes32 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND16 = define
 `OPERAND16 (Register r) s =
        (if register_size r = 16 then GPR16 r else ARB) /\
  OPERAND16 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND16 (Imm16 imm16) s = rvalue imm16 /\
  OPERAND16 (Memop w ea) s =
       (if w = Word then memory :> bytes16 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND8 = define
 `OPERAND8 (Register r) s =
        (if register_size r = 8 then GPR8 r else ARB) /\
  OPERAND8 (Imm8 imm8) s = rvalue imm8 /\
  OPERAND8 (Memop w ea) s =
       (if w = Byte then memory :> bytes8 (bsid_semantics ea s)
        else ARB)`;;

(* ------------------------------------------------------------------------- *)
(* Stating assumptions about instruction decoding                            *)
(* ------------------------------------------------------------------------- *)

let x86_decode = new_definition `x86_decode s pc (len,inst) <=>
  ?l. bytes_loaded s pc l /\ LENGTH l = len /\ decode l = SOME (inst, [])`;;

let X86_DECODE_CONS = prove
 (`!s pc l i l' n.
   bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
   x86_decode s (word pc) (n,i) /\ bytes_loaded s (word (pc + n)) l'`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun bl -> DISCH_THEN (fun th ->
    let th1,th2 = CONJ_PAIR (REWRITE_RULE [decode_len] th) in
    let th1 = MATCH_MP
      (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) th1 in
    C CHOOSE_THEN th1 (fun th ->
      let th3,th4 = CONJ_PAIR th in
      REWRITE_TAC [SYM (REWRITE_RULE [EQ_ADD_LCANCEL]
        (CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [ADD_SYM]))
          ((REWRITE_RULE [th3; LENGTH_APPEND] th2))))] THEN
      let bl1,bl2 = CONJ_PAIR (REWRITE_RULE [th3; bytes_loaded_append] bl) in
      REWRITE_TAC [x86_decode; WORD_ADD; bl2] THEN
      EXISTS_TAC `l'':byte list` THEN REWRITE_TAC [bl1;
        REWRITE_RULE [APPEND_NIL] (SPEC `[]:byte list` th4)]))));;

let x86_decode_unique = prove
 (`!s pc x y. x86_decode s pc x ==> x86_decode s pc y ==> x = y`,
  REWRITE_TAC [FORALL_PAIR_THM; x86_decode] THEN REPEAT GEN_TAC THEN
  SPECL_TAC [`p1:num`; `p1':num`; `p2:instruction`; `p2':instruction`] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [METIS_TAC []; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [d2;l2;b2; d1;l1;b1; h] ->
    let th = MATCH_MP exists_list_split (REWRITE_RULE [SYM l2] h) in
    REPEAT_TCL CHOOSE_THEN (fun th ->
      let th1,th2 = CONJ_PAIR th in
      let th3,th4 = CONJ_PAIR (REWRITE_RULE [th1; bytes_loaded_append] b2) in
      let th = MP (MATCH_MP (MATCH_MP bytes_loaded_unique b1) th3)
        (TRANS l1 (SYM th2)) in
      let d1 = REWRITE_RULE [th; APPEND_NIL; UNWIND_THM1] (MATCH_MP
        (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) d1) in
      let d2 = REWRITE_RULE [th1; d1; OPTION_INJ; PAIR_EQ] d2 in
      REWRITE_TAC [d2;
        REWRITE_RULE [th1; d2; APPEND_NIL; SYM th; l1] l2]) th));;

let X86_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num` in
  let rec go th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3 = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc)
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)) in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> CONJUNCT1 th'
    | _ -> let dth,bth = CONJ_PAIR th' in CONJ dth (go bth) in
  GENL [`s:x86state`; `pc:num`] o DISCH_ALL o go o
    (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
    AP_TERM `bytes_loaded s (word pc)`;;

let X86_MK_EXEC_RULE th0 =
  let th0 = INST [`pc':num`,`pc:num`] (SPEC_ALL th0) in
  let th1 = AP_TERM `LENGTH:byte list->num` th0 in
  let th2 =
    (REWRITE_CONV [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
      LENGTH; LENGTH_APPEND] THENC NUM_REDUCE_CONV) (rhs (concl th1)) in
  CONJ (TRANS th1 th2) (X86_DECODES_THM th0);;

(* ------------------------------------------------------------------------- *)
(* Execution of a single instruction.                                        *)
(* ------------------------------------------------------------------------- *)

(*** note that this is in 64-bit mode (e.g. matters for ROL masking) ***)

(*** We also only support relative jump  at the moment ***)

let x86_execute = define
 `x86_execute instr s =
    match instr with
      ADC dest src ->
        (match operand_size dest with
           64 -> x86_ADC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADC (OPERAND8 dest s) (OPERAND8 src s)) s
    | ADCX dest src ->
        (match operand_size dest with
           64 -> x86_ADCX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADCX (OPERAND32 dest s) (OPERAND32 src s)) s
    | ADD dest src ->
        (match operand_size dest with
           64 -> x86_ADD (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADD (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADD (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADD (OPERAND8 dest s) (OPERAND8 src s)) s
    | ADOX dest src ->
        (match operand_size dest with
           64 -> x86_ADOX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADOX (OPERAND32 dest s) (OPERAND32 src s)) s
    | AND dest src ->
        (match operand_size dest with
           64 -> x86_AND (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_AND (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_AND (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_AND (OPERAND8 dest s) (OPERAND8 src s)) s
    | BSF dest src ->
        (match operand_size dest with
           64 -> x86_BSF (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSF (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSF (OPERAND16 dest s) (OPERAND16 src s)) s
    | BSR dest src ->
        (match operand_size dest with
           64 -> x86_BSR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSR (OPERAND16 dest s) (OPERAND16 src s)) s
    | BSWAP dest ->
        (match operand_size dest with
           64 -> x86_BSWAP (OPERAND64 dest s)
         | 32 -> x86_BSWAP (OPERAND32 dest s)) s
    | BT dest src ->
        (match operand_size dest with
           64 -> x86_BT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BT (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BT (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTC dest src ->
        (match operand_size dest with
           64 -> x86_BTC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTC (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTR dest src ->
        (match operand_size dest with
           64 -> x86_BTR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTR (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTS dest src ->
        (match operand_size dest with
           64 -> x86_BTS (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTS (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTS (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTS (OPERAND8 dest s) (OPERAND8 src s)) s
    | CALL off ->
        (let ip' = word_add (read RIP s)
                            (read (OPERAND64 off s) s) in
         x86_CALL ip' s)
    | CALL_ABSOLUTE target ->
        x86_CALL target s
    | CLC ->
        x86_CLC s
    | CMC ->
        x86_CMC s
    | CMOV cc dest src ->
        (match operand_size dest with
           64 -> x86_CMOV cc (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMOV cc (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMOV cc (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMOV cc (OPERAND8 dest s) (OPERAND8 src s)) s
    | CMP dest src ->
        (match operand_size dest with
           64 -> x86_CMP (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMP (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMP (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMP (OPERAND8 dest s) (OPERAND8 src s)) s
    | DEC dest ->
        (match operand_size dest with
           64 -> x86_DEC (OPERAND64 dest s)
         | 32 -> x86_DEC (OPERAND32 dest s)
         | 16 -> x86_DEC (OPERAND16 dest s)
         | 8 -> x86_DEC (OPERAND8 dest s)) s
    | DIV2 (dest1,dest2) (src1,src2) src3 ->
        (match operand_size dest1 with
           64 -> x86_DIV2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                          (OPERAND64 src1 s,OPERAND64 src2 s)
                          (OPERAND64 src3 s)
         | 32 -> x86_DIV2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                          (OPERAND32 src1 s,OPERAND32 src2 s)
                          (OPERAND32 src3 s)
         | 16 -> x86_DIV2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                          (OPERAND16 src1 s,OPERAND16 src2 s)
                          (OPERAND16 src3 s)
         | 8 -> x86_DIV2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                         (OPERAND8 src1 s,OPERAND8 src2 s)
                         (OPERAND8 src3 s)) s
    | IMUL3 dest (src1,src2) ->
        (match operand_size dest with
           64 -> x86_IMUL3 (OPERAND64 dest s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_IMUL3 (OPERAND32 dest s)
                           (OPERAND32 src1 s, OPERAND32 src2 s)
         | 16 -> x86_IMUL3 (OPERAND16 dest s)
                           (OPERAND16 src1 s,OPERAND16 src2 s)
         | 8 -> x86_IMUL3 (OPERAND8 dest s)
                          (OPERAND8 src1 s,OPERAND8 src2 s)) s
    | IMUL2 (dest1,dest2) src ->
        (match operand_size dest2 with
           64 -> x86_IMUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                          (OPERAND64 src s)
         | 32 -> x86_IMUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                          (OPERAND32 src s)
         | 16 -> x86_IMUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                          (OPERAND16 src s)
         | 8 -> x86_IMUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                          (OPERAND8 src s)) s
    | INC dest ->
        (match operand_size dest with
           64 -> x86_INC (OPERAND64 dest s)
         | 32 -> x86_INC (OPERAND32 dest s)
         | 16 -> x86_INC (OPERAND16 dest s)
         | 8 -> x86_INC (OPERAND8 dest s)) s
    | LZCNT dest src ->
        (match operand_size dest with
           64 -> x86_LZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_LZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_LZCNT (OPERAND16 dest s) (OPERAND16 src s)) s
    | JUMP cc off ->
        (RIP :=
           if condition_semantics cc s
           then word_add (read RIP s)
                         (read (OPERAND64 off s) s)
           else read RIP s) s
    | LEA dest bsid ->
        (match operand_size dest with
          64 -> (OPERAND64 dest s) := (bsid_semantics bsid s)
        | 32 -> (OPERAND32 dest s) := word_sx(bsid_semantics bsid s)
        | 16 -> (OPERAND16 dest s) := word_sx(bsid_semantics bsid s)
        | 8 -> (OPERAND8 dest s) := word_sx(bsid_semantics bsid s)) s
    | MOV dest src ->
        (match operand_size dest with
           64 -> x86_MOV (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_MOV (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_MOV (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_MOV (OPERAND8 dest s) (OPERAND8 src s)) s
    | MOVSX dest src ->
        (match (operand_size dest,operand_size src) with
           (64,32) -> x86_MOVSX (OPERAND64 dest s) (OPERAND32 src s)
         | (64,16) -> x86_MOVSX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVSX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,16) -> x86_MOVSX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVSX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVSX (OPERAND16 dest s) (OPERAND8 src s)) s
    | MOVZX dest src ->
        (match (operand_size dest,operand_size src) with
           (64,16) -> x86_MOVZX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVZX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,16) -> x86_MOVZX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVZX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVZX (OPERAND16 dest s) (OPERAND8 src s)) s
    | MUL2 (dest1,dest2) src ->
        (match operand_size dest2 with
           64 -> x86_MUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                         (OPERAND64 src s)
         | 32 -> x86_MUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                         (OPERAND32 src s)
         | 16 -> x86_MUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                         (OPERAND16 src s)
         | 8 -> x86_MUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                         (OPERAND8 src s)) s
    | MULX4 (dest1,dest2) (src1,src2) ->
        (match operand_size dest2 with
           64 -> x86_MULX4 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_MULX4 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                           (OPERAND32 src1 s,OPERAND32 src2 s)) s
    | NEG dest ->
        (match operand_size dest with
           64 -> x86_NEG (OPERAND64 dest s)
         | 32 -> x86_NEG (OPERAND32 dest s)
         | 16 -> x86_NEG (OPERAND16 dest s)
         | 8 -> x86_NEG (OPERAND8 dest s)) s
    | NOP ->
        x86_NOP s
    | NOT dest ->
        (match operand_size dest with
           64 -> x86_NOT (OPERAND64 dest s)
         | 32 -> x86_NOT (OPERAND32 dest s)
         | 16 -> x86_NOT (OPERAND16 dest s)
         | 8 -> x86_NOT (OPERAND8 dest s)) s
    | OR dest src ->
        (match operand_size dest with
           64 -> x86_OR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_OR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_OR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_OR (OPERAND8 dest s) (OPERAND8 src s)) s
    | POP dest ->
        (match operand_size dest with
           64 -> x86_POP (OPERAND64 dest s)
         | 16 -> x86_POP (OPERAND16 dest s)) s
    | PUSH src ->
        (match operand_size src with
           64 -> x86_PUSH (OPERAND64 src s)
         | 16 -> x86_PUSH (OPERAND16 src s)) s
    | RCL dest src ->
        (match operand_size dest with
           64 -> x86_RCL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_RCL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_RCL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | RCR dest src ->
        (match operand_size dest with
           64 -> x86_RCR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_RCR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_RCR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | RET ->
        x86_RET s
    | ROL dest src ->
        (match operand_size dest with
           64 -> x86_ROL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_ROL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_ROL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | ROR dest src ->
        (match operand_size dest with
           64 -> x86_ROR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_ROR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_ROR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | SAR dest src ->
        (match operand_size dest with
           64 -> x86_SAR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SAR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_SAR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_SAR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | SBB dest src ->
        (match operand_size dest with
           64 -> x86_SBB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SBB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SBB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SBB (OPERAND8 dest s) (OPERAND8 src s)) s
    | SET cc dest ->
        (match operand_size dest with
           8 -> x86_SET cc (OPERAND8 dest s)
         | _ -> ARB) s
    | SHL dest src ->
        (match operand_size dest with
           64 -> x86_SHL (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_SHL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_SHL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | SHLD dest src c ->
        (match operand_size dest with
           64 -> x86_SHLD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHLD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 16 -> x86_SHLD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 8 -> x86_SHLD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 64)) s
    | SHR dest src ->
        (match operand_size dest with
           64 -> x86_SHR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 16 -> x86_SHR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 8 -> x86_SHR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)) s
    | SHRD dest src c ->
        (match operand_size dest with
           64 -> x86_SHRD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHRD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 16 -> x86_SHRD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 8 -> x86_SHRD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 64)) s
    | STCF ->
        x86_STC s
    | SUB dest src ->
        (match operand_size dest with
           64 -> x86_SUB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SUB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SUB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SUB (OPERAND8 dest s) (OPERAND8 src s)) s
    | TEST dest src ->
        (match operand_size dest with
           64 -> x86_TEST (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TEST (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TEST (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_TEST (OPERAND8 dest s) (OPERAND8 src s)) s
    | TZCNT dest src ->
        (match operand_size dest with
           64 -> x86_TZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TZCNT (OPERAND16 dest s) (OPERAND16 src s)) s
    | XOR dest src ->
        (match operand_size dest with
           64 -> x86_XOR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_XOR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_XOR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_XOR (OPERAND8 dest s) (OPERAND8 src s)) s
    | _ -> (\s'. F)`;;

(* ------------------------------------------------------------------------- *)
(* Now the basic fetch-decode-execute cycle.                                 *)
(* ------------------------------------------------------------------------- *)

(*** Note that we *always* increment the instruction pointer first. This is
 *** consistent with the fact that relative offsets in JMP, CALL are
 *** relative to the *next* instruction, so we can use current PC in
 *** the execution of control flow instructions.
 ***)

let x86 = define
 `x86 s s' <=>
    ?len instr. x86_decode s (read RIP s) (len,instr) /\
                (RIP := word_add (read RIP s) (word len) ,,
                x86_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Shorthand for the set of all flags for modification lists.                *)
(* ------------------------------------------------------------------------- *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS = [CF; PF; AF; ZF; SF; OF]`;;

(* ------------------------------------------------------------------------- *)
(* Nicer packaging for common patterns.                                      *)
(* ------------------------------------------------------------------------- *)

(*** This is for the "System V AMD64 ABI", i.e. modern unixes     ***)
(*** We don't talk about the stack or FP arguments yet            ***)

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5 /\ read  R9 s = a6) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5) /\
  (C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4) /\
  (C_ARGUMENTS [a1;a2;a3] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3) /\
  (C_ARGUMENTS [a1;a2] s <=>
        read RDI s = a1 /\ read RSI s = a2) /\
  (C_ARGUMENTS [a1] s <=>
        read RDI s = a1) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read RAX`;;

let PRESERVED_GPRS = define
 `PRESERVED_GPRS = [RSP; RBX; RBP; R12; R13; R14; R15]`;;

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS = [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11]`;;

(* ------------------------------------------------------------------------- *)
(* Clausal theorems and other execution assistance.                          *)
(* ------------------------------------------------------------------------- *)

let OPERAND_SIZE_CASES = prove
 (`(match 64 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = a /\
   (match 32 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = b /\
   (match 16 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = c /\
   (match  8 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = d /\
   (match (64,32) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = a /\
   (match (64,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = b /\
   (match (64,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = c /\
   (match (32,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = d /\
   (match (32,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = e /\
   (match (16,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = f /\
   (match (64,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = b /\
   (match (64,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = c /\
   (match (32,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = d /\
   (match (32,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = e /\
   (match (16,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> d | (32,8) -> e  | (16,8) -> f) = f`,
  CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let X86_EXECUTE =
  CONV_RULE (TOP_DEPTH_CONV let_CONV)
   (GEN_REWRITE_RULE LAND_CONV [ETA_AX]
     (GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]
        (GEN `s:x86state` x86_execute)));;

let REGISTER_ALIASES =
 [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
  r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
  eax; ecx; edx; ebx; esp; ebp; esi; edi;
  r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
  ax; cx; dx; bx; sp; bp; si; di; ah;
  al; ch; cl; dh; dl; bh; bl];;

let OPERAND_SIZE_CONV =
  let topconv = GEN_REWRITE_CONV I [operand_size]
  and botconv = GEN_REWRITE_CONV TOP_DEPTH_CONV (QWORD::REGISTER_ALIASES)
  and midconv = GEN_REWRITE_CONV REPEATC
   [register_size; bytesize; regsize] in
  fun tm ->
    match tm with
      Comb(Const("operand_size",_),_)->
          (botconv THENC topconv THENC midconv) tm
    | _ -> failwith "OPERAND_SIZE_CONV";;

let BSID_CLAUSES_GEN = prove
 (`bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) (SOME(Gpr r2 Full_64)) k d) s =
   word_add (read (registers :> element r1) s)
            (word (2 EXP (val k) * val(read (registers :> element r2) s) +
                   val d)) /\
   bsid_semantics (Bsid NONE (SOME(Gpr r2 Full_64)) k d) s =
   word_add (word 0)
    (word (2 EXP (val k) * val(read (registers :> element r2) s) + val d)) /\
   bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) NONE k d) s =
   word_add (read (registers :> element r1) s) d`,
  REWRITE_TAC[bsid_semantics; GPR] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[WORD_ADD_ASSOC; WORD_VAL] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN TRY BINOP_TAC THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL] THEN TRY AP_TERM_TAC THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[read; asnumber; through] THEN REWRITE_TAC[WORD_VAL]);;

let BSID_SEMANTICS_CONV =
  let coreconv =
    GEN_REWRITE_CONV (LAND_CONV o TRY_CONV)
     [base_displacement; base_scaled_index;
      base_scaled_index_displacement] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
      r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15] THENC
    GEN_REWRITE_CONV I [BSID_CLAUSES_GEN] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     (map GSYM [RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
                R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15]) THENC
    ONCE_DEPTH_CONV WORD_VAL_CONV THENC
    ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [ARITH_RULE `n + 0 = n`] in
  fun tm ->
   (match tm with
      Comb(Comb(Const("bsid_semantics",_),_),_) -> coreconv tm
    | _ -> failwith "BSID_SEMANTICS_CONV");;

let BSID_NORMALIZE_TAC =
  let pth_gen = prove
   (`word(8 * i + 0):int64 = word(8 * i) /\
     word(8 * i + 8):int64 = word(8 * (i + 1)) /\
     word(8 * i + 16):int64 = word(8 * (i + 2))`,
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
  and pth_spc = prove
   (`0 < i ==> word(8 * i + 18446744073709551608):int64 = word(8 * (i - 1))`,
    SPEC_TAC(`i:num`,`i:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[LT_REFL; SUC_SUB1] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `8 * SUC i + 18446744073709551608 =
      1 * 2 EXP 64 + 8 * i`]) in
  let rule_spc = PART_MATCH (lhand o rand) pth_spc in
  let siderule =
    let siderule_1 asl tm = find (fun th -> concl th = tm) asl
    and rules = map (PART_MATCH rand o ARITH_RULE)
     [`1 <= n ==> 0 < n`; `~(n = 0) ==> 0 < n`;  `m < n ==> 0 < n - m`] in
    fun asl tm ->
      tryfind (fun rule ->
            let th = rule tm in
            MP th (siderule_1 asl (lhand(concl th)))) rules in
  let fullconv(asl,w) tm =
    if not(free_in tm w) then failwith "rule" else
    let th = rule_spc tm in
    MP th (siderule (map snd asl) (lhand(concl th))) in
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [pth_gen] THEN
  W(fun (asl,w) -> CONV_TAC(ONCE_DEPTH_CONV(fullconv(asl,w))));;

let BSID_CLAUSES = prove
 (`bsid_semantics (%%(rax,d)) s = word_add (read RAX s) (word d) /\
   bsid_semantics (%%(rcx,d)) s = word_add (read RCX s) (word d) /\
   bsid_semantics (%%(rdx,d)) s = word_add (read RDX s) (word d) /\
   bsid_semantics (%%(rbx,d)) s = word_add (read RBX s) (word d) /\
   bsid_semantics (%%(rsp,d)) s = word_add (read RSP s) (word d) /\
   bsid_semantics (%%(rbp,d)) s = word_add (read RBP s) (word d) /\
   bsid_semantics (%%(rsi,d)) s = word_add (read RSI s) (word d) /\
   bsid_semantics (%%(rdi,d)) s = word_add (read RDI s) (word d) /\
   bsid_semantics (%%( r8,d)) s = word_add (read  R8 s) (word d) /\
   bsid_semantics (%%( r9,d)) s = word_add (read  R9 s) (word d) /\
   bsid_semantics (%%(r10,d)) s = word_add (read R10 s) (word d) /\
   bsid_semantics (%%(r11,d)) s = word_add (read R11 s) (word d) /\
   bsid_semantics (%%(r12,d)) s = word_add (read R12 s) (word d) /\
   bsid_semantics (%%(r13,d)) s = word_add (read R13 s) (word d) /\
   bsid_semantics (%%(r14,d)) s = word_add (read R14 s) (word d) /\
   bsid_semantics (%%(r15,d)) s = word_add (read R15 s) (word d)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15] THEN
  REWRITE_TAC[BSID_CLAUSES_GEN; base_displacement]);;

let OPERAND_CLAUSES_GEN = prove
 (`OPERAND64 (%rax) s = RAX /\
   OPERAND64 (%rcx) s = RCX /\
   OPERAND64 (%rdx) s = RDX /\
   OPERAND64 (%rbx) s = RBX /\
   OPERAND64 (%rsp) s = RSP /\
   OPERAND64 (%rbp) s = RBP /\
   OPERAND64 (%rsi) s = RSI /\
   OPERAND64 (%rdi) s = RDI /\
   OPERAND64 (% r8) s =  R8 /\
   OPERAND64 (% r9) s =  R9 /\
   OPERAND64 (%r10) s = R10 /\
   OPERAND64 (%r11) s = R11 /\
   OPERAND64 (%r12) s = R12 /\
   OPERAND64 (%r13) s = R13 /\
   OPERAND64 (%r14) s = R14 /\
   OPERAND64 (%r15) s = R15 /\
   OPERAND64 (## n) s = rvalue(word_sx(word n:32 word)) /\
   OPERAND64 (Imm64 w64) s = rvalue w64 /\
   OPERAND64 (Imm32 w32) s = rvalue(word_sx w32) /\
   OPERAND64 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND64 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND64 (QWORD bsid) s = memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND64 (Memop Quadword bsid) s =
    memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND32 (%eax) s = RAX :> zerotop_32 /\
   OPERAND32 (%ecx) s = RCX :> zerotop_32 /\
   OPERAND32 (%edx) s = RDX :> zerotop_32 /\
   OPERAND32 (%ebx) s = RBX :> zerotop_32 /\
   OPERAND32 (%esp) s = RSP :> zerotop_32 /\
   OPERAND32 (%ebp) s = RBP :> zerotop_32 /\
   OPERAND32 (%esi) s = RSI :> zerotop_32 /\
   OPERAND32 (%edi) s = RDI :> zerotop_32 /\
   OPERAND32 (%r8d) s =  R8 :> zerotop_32 /\
   OPERAND32 (%r9d) s =  R9 :> zerotop_32 /\
   OPERAND32 (%r10d) s = R10 :> zerotop_32 /\
   OPERAND32 (%r11d) s = R11 :> zerotop_32 /\
   OPERAND32 (%r12d) s = R12 :> zerotop_32 /\
   OPERAND32 (%r13d) s = R13 :> zerotop_32 /\
   OPERAND32 (%r14d) s = R14 :> zerotop_32 /\
   OPERAND32 (%r15d) s = R15 :> zerotop_32 /\
   OPERAND32 (## n) s = rvalue(word n:32 word) /\
   OPERAND32 (Imm32 w32) s = rvalue w32 /\
   OPERAND32 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND32 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND32 (Memop Doubleword bsid) s =
    memory :> bytes32 (bsid_semantics bsid s) /\
   OPERAND16 (%ax) s = AX /\
   OPERAND16 (%cx) s = CX /\
   OPERAND16 (%dx) s = DX /\
   OPERAND16 (%bx) s = BX /\
   OPERAND16 (%sp) s = SP /\
   OPERAND16 (%bp) s = BP /\
   OPERAND16 (%si) s = SI /\
   OPERAND16 (%di) s = DI /\
   OPERAND16 (Imm16 w16) s = rvalue w16 /\
   OPERAND16 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND16 (Memop Word bsid) s =
    memory :> bytes16 (bsid_semantics bsid s) /\
   OPERAND8 (%ah) s = AH /\
   OPERAND8 (%al) s = AL /\
   OPERAND8 (%ch) s = CH /\
   OPERAND8 (%cl) s = CL /\
   OPERAND8 (%dh) s = DH /\
   OPERAND8 (%dl) s = DL /\
   OPERAND8 (%bh) s = BH /\
   OPERAND8 (%bl) s = BL /\
   OPERAND8 (Imm8 w8) s = rvalue w8 /\
   OPERAND8 (Memop Byte bsid) s =
    memory :> bytes8 (bsid_semantics bsid s)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15;
              eax; ecx; edx; ebx; esp; ebp; esi; edi;
              r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
              ax; cx; dx; bx; sp; bp; si; di; ah;
              al; ch; cl; dh; dl; bh; bl;
              EAX; ECX; EDX; EBX; ESP; EBP; ESI; EDI;
              R8D; R9D; R10D; R11D; R12D; R13D; R14D; R15D;
              AX; CX; DX; BX; SP; BP; SI; DI;
              AH; AL; BH; BL; CH; CL; DH; DL] THEN
  REWRITE_TAC[simple_immediate; base_displacement; QWORD] THEN
  REWRITE_TAC[OPERAND64; OPERAND32; OPERAND16; OPERAND8;
              register_size; regsize; GPR64; GPR32_Z; GPR32; GPR16; GPR8] THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC]);;

let OPERAND_CLAUSES = prove
 (`OPERAND64 (%rax) s = RAX /\
   OPERAND64 (%rcx) s = RCX /\
   OPERAND64 (%rdx) s = RDX /\
   OPERAND64 (%rbx) s = RBX /\
   OPERAND64 (%rsp) s = RSP /\
   OPERAND64 (%rbp) s = RBP /\
   OPERAND64 (%rsi) s = RSI /\
   OPERAND64 (%rdi) s = RDI /\
   OPERAND64 (% r8) s =  R8 /\
   OPERAND64 (% r9) s =  R9 /\
   OPERAND64 (%r10) s = R10 /\
   OPERAND64 (%r11) s = R11 /\
   OPERAND64 (%r12) s = R12 /\
   OPERAND64 (%r13) s = R13 /\
   OPERAND64 (%r14) s = R14 /\
   OPERAND64 (%r15) s = R15 /\
   OPERAND64 (## n) s = rvalue(word_sx(word n:32 word)) /\
   OPERAND64 (Imm64 w64) s = rvalue w64 /\
   OPERAND64 (Imm32 w32) s = rvalue(word_sx w32) /\
   OPERAND64 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND64 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND64 (QWORD(%%(rax,d))) s =
     memory :> bytes64(word_add (read RAX s) (word d)) /\
   OPERAND64 (QWORD(%%(rcx,d))) s =
     memory :> bytes64(word_add (read RCX s) (word d)) /\
   OPERAND64 (QWORD(%%(rdx,d))) s =
     memory :> bytes64(word_add (read RDX s) (word d)) /\
   OPERAND64 (QWORD(%%(rbx,d))) s =
     memory :> bytes64(word_add (read RBX s) (word d)) /\
   OPERAND64 (QWORD(%%(rsp,d))) s =
     memory :> bytes64(word_add (read RSP s) (word d)) /\
   OPERAND64 (QWORD(%%(rbp,d))) s =
     memory :> bytes64(word_add (read RBP s) (word d)) /\
   OPERAND64 (QWORD(%%(rsi,d))) s =
     memory :> bytes64(word_add (read RSI s) (word d)) /\
   OPERAND64 (QWORD(%%(rdi,d))) s =
     memory :> bytes64(word_add (read RDI s) (word d)) /\
   OPERAND64 (QWORD(%%( r8,d))) s =
     memory :> bytes64(word_add (read  R8 s) (word d)) /\
   OPERAND64 (QWORD(%%( r9,d))) s =
     memory :> bytes64(word_add (read  R9 s) (word d)) /\
   OPERAND64 (QWORD(%%(r10,d))) s =
     memory :> bytes64(word_add (read R10 s) (word d)) /\
   OPERAND64 (QWORD(%%(r11,d))) s =
     memory :> bytes64(word_add (read R11 s) (word d)) /\
   OPERAND64 (QWORD(%%(r12,d))) s =
     memory :> bytes64(word_add (read R12 s) (word d)) /\
   OPERAND64 (QWORD(%%(r13,d))) s =
     memory :> bytes64(word_add (read R13 s) (word d)) /\
   OPERAND64 (QWORD(%%(r14,d))) s =
     memory :> bytes64(word_add (read R14 s) (word d)) /\
   OPERAND64 (QWORD(%%(r15,d))) s =
     memory :> bytes64(word_add (read R15 s) (word d))`,
  REWRITE_TAC[OPERAND_CLAUSES_GEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV BSID_SEMANTICS_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some forms with a comprehensible carry flag; currently 64-bit only.       *)
(* Also 64-bit instantiations of PUSH and POP are much simpler to work with. *)
(* ------------------------------------------------------------------------- *)

let x86_ADC_ALT = prove
 (`x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y + c) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADC] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADCX_ALT = prove
 (`x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         CF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADCX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADOX_ALT = prove
 (`x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         OF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADOX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADD_ALT = prove
 (`x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADD]);;

let x86_SBB_ALT = prove
 (`x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y + c) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SBB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SBB]);;

let x86_SUB_ALT = prove
 (`x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SUB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_CMP_ALT = prove
 (`x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:64 word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_CMP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_POP_ALT = prove
 (`x86_POP dest s =
        let p = read RSP s in
        let x = read (memory :> bytes64 p) s in
        let p' = word_add p (word 8) in
        (RSP := p' ,,
         dest := x) s`,
  REWRITE_TAC[x86_POP; DIMINDEX_64; bytes64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; asword; through; read; write]);;

let x86_PUSH_ALT = prove
 (`x86_PUSH src s =
        let p = read RSP s
        and x = read src s in
        let p' = word_sub p (word 8) in
        (RSP := p' ,,
         memory :> bytes64 p' := x) s`,
  REWRITE_TAC[x86_PUSH; DIMINDEX_64; bytes64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; asword; through; read; write; seq;
              assign]);;

let x86_CALL_ALT = prove
 (`x86_CALL target s =
        let p = read RSP s
        and x = read RIP s in
        let p' = word_sub p (word 8) in
        (RSP := p' ,,
         memory :> bytes64 p' := x ,,
         RIP := target) s`,
  REWRITE_TAC[x86_CALL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[x86_PUSH_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign] THEN MESON_TAC[]);;

(*** Just a conceptual observation, not actually used ***)

let x86_RET_POP_RIP = prove
 (`x86_RET = x86_POP RIP`,
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:x86state` THEN
  REWRITE_TAC[x86_POP_ALT; x86_RET] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let X86_OPERATION_CLAUSES =
  map (CONV_RULE(TOP_DEPTH_CONV let_CONV) o SPEC_ALL)
   [x86_ADC_ALT; x86_ADCX_ALT; x86_ADOX_ALT;
    x86_ADD_ALT; x86_AND; x86_BSF; x86_BSR; x86_BSWAP;
    x86_BT; x86_BTC; x86_BTR; x86_BTS;
    x86_CALL_ALT; x86_CLC; x86_CMC; x86_CMOV; x86_CMP_ALT; x86_DEC;
    x86_DIV2; x86_IMUL; x86_IMUL2; x86_IMUL3; x86_INC; x86_LEA; x86_LZCNT;
    x86_MOV; x86_MOVSX; x86_MOVZX;
    x86_MUL2; x86_MULX4; x86_NEG; x86_NOP; x86_NOT; x86_OR;
    x86_POP_ALT; x86_PUSH_ALT; x86_RCL; x86_RCR; x86_RET; x86_ROL; x86_ROR;
    x86_SAR; x86_SBB_ALT; x86_SET; x86_SHL; x86_SHLD; x86_SHR; x86_SHRD;
    x86_STC; x86_SUB_ALT; x86_TEST; x86_TZCNT; x86_XOR;
    (*** 32-bit backups since the ALT forms are 64-bit only ***)
    INST_TYPE[`:32`,`:N`] x86_ADC;
    INST_TYPE[`:32`,`:N`] x86_SBB];;

(* ------------------------------------------------------------------------- *)
(* Getting CL out of RCX (for variable-length shifts).                       *)
(* ------------------------------------------------------------------------- *)

let READ_CL_RCX = prove
 (`read CL s = word(val(read RCX s) MOD 256)`,
  REWRITE_TAC[CL; CX; ECX; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[bottom_8; bottom_16; bottom_32; bottomhalf] THEN
  REWRITE_TAC[read; subword; VAL_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `64 = 2 EXP 6`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Trivial reassociation and reduction of "word((pc + m) + n)"               *)
(* ------------------------------------------------------------------------- *)

let WORD_NUM_ASSOC_AND_ADD_CONV =
  GEN_REWRITE_CONV I
   [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
  RAND_CONV(RAND_CONV NUM_ADD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Perform symbolic execution of one instruction to reach named state.       *)
(* ------------------------------------------------------------------------- *)

let X86_THM =
  let pth = prove
   (`read RIP s = word pc ==> x86_decode s (word pc) (n,instr) ==>
     (x86 s s' <=> (RIP := word (pc + n) ,, x86_execute instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [x86] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_MESON_TAC[PAIR_EQ; x86_decode_unique]) in
  fun conj th ->
    let th = MATCH_MP pth th in
    let rec go conj = try
      let th1,th2 = CONJ_PAIR conj in
      try MATCH_MP th th1 with Failure _ -> go th2
    with Failure _ -> MATCH_MP th conj in
    CONV_RULE
      (ONCE_DEPTH_CONV
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV))
      (go conj);;

let X86_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o MATCH_MP bytes_loaded_update o CONJUNCT1;;

let X86_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o map (MATCH_MP bytes_loaded_update o CONJUNCT1);;

let X86_UNDEFINED_GEN_TAC =
  let rec chundef avoids n =
    let v = "undefined_"^string_of_int n in
    if mem v avoids then chundef avoids (n+1) else v in
  fun (asl,w) ->
    try let ty = snd(dest_var(fst(dest_forall w))) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let x' = chundef (map (fst o dest_var) avoids) 1 in
        X_GEN_TAC (mk_var(x',ty)) (asl,w)
      with Failure _ -> failwith "X86_UNDEFINED_GEN_TAC";;

let X86_UNDEFINED_CHOOSE_TAC =
  GEN_REWRITE_TAC I [LEFT_IMP_EXISTS_THM] THEN X86_UNDEFINED_GEN_TAC;;

(*** This is to force more aggressive use of assumptions and
 *** simplification if we have a conditional indicative of a
 *** possible exception. Currently this only arises in the
 *** division instruction for cases we are verifying
 ***)

let X86_FORCE_CONDITIONAL_CONV =
  let trigger t = is_comb t && is_cond(rator t) in
  fun ths ->
     let baseconv =
       GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (ONCE_DEPTH_CONV DIMINDEX_CONV))) THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (DEPTH_CONV WORD_NUM_RED_CONV))) THENC
       GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths THENC
       GEN_REWRITE_CONV RATOR_CONV [COND_CLAUSES] in
     let chconv t = if trigger t then baseconv t else failwith "baseconv" in
     fun tm -> if trigger tm then (REPEATC chconv THENC TRY_CONV BETA_CONV) tm
               else REFL tm;;

let X86_CONV execth2 ths tm =
  let th = tryfind (MATCH_MP execth2) ths in
  let eth = tryfind (fun th2 -> GEN_REWRITE_CONV I [X86_THM th th2] tm) ths in
  (K eth THENC
   REWRITE_CONV[X86_EXECUTE] THENC
   ONCE_DEPTH_CONV OPERAND_SIZE_CONV THENC
   REWRITE_CONV[condition_semantics] THENC
   REWRITE_CONV[OPERAND_SIZE_CASES] THENC
   REWRITE_CONV[OPERAND_CLAUSES_GEN] THENC
   ONCE_DEPTH_CONV BSID_SEMANTICS_CONV THENC
   REWRITE_CONV X86_OPERATION_CLAUSES THENC
   REWRITE_CONV[READ_RVALUE; ASSIGN_ZEROTOP_32; READ_CL_RCX;
                READ_ZEROTOP_32; WRITE_ZEROTOP_32] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   REWRITE_CONV[SEQ; condition_semantics] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [UNDEFINED_VALUE; UNDEFINED_VALUES; SEQ_ID] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [ASSIGNS_PULL_THM] THENC
   REWRITE_CONV[ASSIGNS_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [SEQ_PULL_THM; BETA_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV[assign; seq; UNWIND_THM1; BETA_THM] THENC
   REWRITE_CONV[] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   X86_FORCE_CONDITIONAL_CONV ths THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let X86_BASIC_STEP_TAC =
  let x86_tm = `x86` and x86_ty = `:x86state` in
  fun execth2 sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,x86_ty) in
    let atm = mk_comb(mk_comb(x86_tm,sv),sv') in
    let eth = X86_CONV execth2 (map snd asl) atm in
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
      REPEAT X86_UNDEFINED_CHOOSE_TAC]) (asl,w);;

let X86_STEP_TAC (execth::subths) sname =
  let execth1,execth2 = CONJ_PAIR execth in

  (*** This does the basic decoding setup ***)

  X86_BASIC_STEP_TAC execth2 sname THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update execth1) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP bytes_loaded_update o CONJUNCT1) subths THEN

  (*** This part produces any updated versions of existing asms ***)

  ASSUMPTION_STATE_UPDATE_TAC THEN

  (*** Produce updated "MAYCHANGE" assumption ***)

  MAYCHANGE_STATE_UPDATE_TAC THEN

  (*** This adds state component theorems for the updates ***)
  (*** Could also assume th itself but I throw it away   ***)

  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    STRIP_TAC);;

let X86_VERBOSE_STEP_TAC exth sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  X86_STEP_TAC [exth] sname g;;

let X86_VERBOSE_SUBSTEP_TAC exths sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  X86_STEP_TAC exths sname g;;

(* ------------------------------------------------------------------------- *)
(* Throw away assumptions according to patterns.                             *)
(* ------------------------------------------------------------------------- *)

let DISCARD_ASSUMPTIONS_TAC P =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check P));;

let DISCARD_MATCHING_ASSUMPTIONS pats =
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> exists (fun ptm -> can (term_match [] ptm) (concl th)) pats);;

let DISCARD_FLAGS_TAC =
  DISCARD_MATCHING_ASSUMPTIONS
   [`read CF s = y`; `read PF s = y`; `read AF s = y`;
    `read ZF s = y`; `read SF s = y`; `read OF s = y`];;

let DISCARD_STATE_TAC s =
  DISCARD_ASSUMPTIONS_TAC (free_in (mk_var(s,`:x86state`)) o concl);;

let DISCARD_OLDSTATE_TAC s =
  let v = mk_var(s,`:x86state`) in
  let rec badread okvs tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) -> not(mem s okvs)
    | Comb(s,t) -> badread okvs s || badread okvs t
    | Abs(v,t) -> badread (v::okvs) t
    | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(badread [v] o concl);;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let X86_SINGLE_STEP_TAC th s =
  time (X86_VERBOSE_STEP_TAC th s) THEN DISCARD_OLDSTATE_TAC s;;

let X86_VACCSTEP_TAC th aflag s =
  X86_VERBOSE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC) else ALL_TAC);;

let X86_XACCSTEP_TAC th excs aflag s =
  X86_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

let X86_ACCSTEP_TAC th aflag s =
  X86_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC) else ALL_TAC);;

let X86_VSTEPS_TAC th snums =
  MAP_EVERY (X86_VERBOSE_STEP_TAC th) (statenames "s" snums);;

let X86_STEPS_TAC th snums =
  MAP_EVERY (X86_SINGLE_STEP_TAC th) (statenames "s" snums);;

let X86_VACCSTEPS_TAC th anums snums =
  MAP_EVERY (fun n -> X86_VACCSTEP_TAC th (mem n anums) ("s"^string_of_int n))
            snums;;

let X86_XACCSTEPS_TAC th excs anums snums =
  MAP_EVERY
   (fun n -> X86_XACCSTEP_TAC th excs (mem n anums) ("s"^string_of_int n))
   snums;;

let X86_ACCSTEPS_TAC th anums snums =
  MAP_EVERY (fun n -> X86_ACCSTEP_TAC th (mem n anums) ("s"^string_of_int n))
            snums;;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let X86_SIM_TAC execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

let X86_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures step P Q C ==> eventually R s      *)
(* ------------------------------------------------------------------------- *)

let (X86_BIGSTEP_TAC:thm->string->tactic) =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
     ==> ensures step P Q C ==> eventually step R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S. eventually step P s ==> eventually step Q s)
      ==> eventually step P s ==> eventually step Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
    ASM_REWRITE_TAC[]) in
  fun execth sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP bytes_loaded_update (CONJUNCT1 execth)) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN DISCARD_OLDSTATE_TAC sname])
    (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a subroutine, instantiating it from the state.                   *)
(* ------------------------------------------------------------------------- *)

let X86_SUBROUTINE_SIM_TAC (machinecode,execth,offset,submachinecode,subth) =
  let subimpth =
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
      (MATCH_MP bytes_loaded_of_append3
        (TRANS machinecode (N_SUBLIST_CONV (SPEC_ALL submachinecode) offset
           (rhs(concl machinecode)))))) in
  fun ilist0 n ->
    let sname = "s"^string_of_int(n-1)
    and sname' = "s"^string_of_int n in
    let svar = mk_var(sname,`:x86state`)
    and svar0 = mk_var("s",`:x86state`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(SPECL ilist subth) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV
       NORMALIZE_RELATIVE_ADDRESS_CONV))] THEN
    X86_BIGSTEP_TAC execth sname' THENL
     [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC];;

let X86_SUBROUTINE_SIM_ABBREV_TAC tupper ilist0 =
  let tac = X86_SUBROUTINE_SIM_TAC tupper ilist0 in
  fun comp0 abn n (asl,w) ->
    let svar0 = mk_var("s",`:x86state`)
    and svar0' = mk_var("s'",`:x86state`)
    and svar = mk_var("s"^string_of_int(n-1),`:x86state`)
    and svar' = mk_var("s"^string_of_int n,`:x86state`) in
    let comp1 =
      rand(concl(PURE_ONCE_REWRITE_CONV (map snd asl)
        (vsubst[svar,svar0;svar',svar0'] comp0))) in
    (tac n THEN
     ABBREV_TAC(mk_eq(mk_var(abn,type_of comp1),comp1))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Fix up call/return boilerplate given core correctness.                    *)
(* ------------------------------------------------------------------------- *)

let X86_ADD_RETURN_NOSTACK_TAC =
  let lemma1 = prove
   (`ensures step P Q R /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures step P (\s. Q s /\ Q' s) R`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let lemma2 = prove
   (`C' subsumed C /\
     C ,, C = C /\
     (!s s'. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s /\
             Q s' /\ C' s s'
             ==> progdata s' /\ stackdata s' /\ retdata s') /\
     ensures step (\s. progdata s /\ stackdata s /\ retdata s /\ Q s) R C
     ==> ensures step (\s. progdata s /\ pcdata s /\ P s) Q C'
          ==> ensures step
               (\s. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s)
               R C`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ p /\ q ==> r ==> s <=> a ==> b ==> p ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`]
     ENSURES_TRANS_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ENSURES_FRAME_SUBSUMED)) THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r /\ s <=> s /\ p /\ q /\ r`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    MP_TAC coreth THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MAYCHANGE_IDEMPOT_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP bytes_loaded_update (CONJUNCT1 execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      X86_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Version with register save/restore and stack adjustment.                  *)
(* ------------------------------------------------------------------------- *)

let X86_ADD_RETURN_STACK_TAC =
  let mono2lemma = MESON[]
   `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)` in
  fun execth coreth reglist stackoff ->
    let regs = dest_list reglist in
    let n = let n0 = length regs in if 8 * n0 = stackoff then n0 else n0 + 1 in
    MP_TAC coreth THEN
    REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
    (if free_in `RSP` (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC execth (1--n) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC execth ("s"^string_of_int(n+1)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    X86_STEPS_TAC execth ((n+2)--(2*n+2)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Bounding rules (useful to show carries are zero sometimes).               *)
(* ------------------------------------------------------------------------- *)

let BOUND_RULE =
  let dest_add = dest_binop `( + ):num->num->num`
  and dest_mul = dest_binop `( * ):num->num->num`
  and le_tm = `( <= ):num->num->bool`
  and pth = prove
   (`val(x:int64) <= 18446744073709551615`,
    MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
    ARITH_TAC)
  and qth = ARITH_RULE `!n:num. n <= n` in
  let gives_bound tm th =
    let ptm = concl th in
    let rtm = mk_comb(le_tm,tm) in
    if is_comb ptm && rator ptm = rtm && is_numeral(rand ptm)
    then th else failwith "gives_bound" in
  let rec bound bths tm =
    if is_numeral tm then SPEC tm qth else
    try
      tryfind (gives_bound tm) bths
    with Failure _ -> try
      PART_MATCH lhand BITVAL_BOUND tm
    with Failure _ -> try
      PART_MATCH lhand pth tm
    with Failure _ -> try
      let ltm,rtm = dest_add tm in
      let lth = bound bths ltm and rth = bound bths rtm in
      CONV_RULE (RAND_CONV NUM_ADD_CONV) (MATCH_MP LE_ADD2 (CONJ lth rth))
   with Failure _ -> try
      let ltm,rtm = dest_mul tm in
      let lth = bound bths ltm and rth = bound bths rtm in
      CONV_RULE (RAND_CONV NUM_MULT_CONV) (MATCH_MP LE_MULT2 (CONJ lth rth))
   with Failure _ -> failwith "BOUND_RULE" in
  bound;;

let DERIVE_BOUNDS_RULE =
  let prule = (MATCH_MP o prove)
   (`2 EXP 64 * x + val(y:int64) <= b
     ==> x <= b DIV 18446744073709551616 /\
         val y <= MIN 18446744073709551615 b`,
    MP_TAC(ISPEC `y:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
    ARITH_TAC) in
  let rec DERIVE_BOUNDS_RULE bths eths =
    match eths with
       [] -> bths
    | eth::oeths ->
        let newths =
          try let etm = concl eth in
              let ltm,rtm = dest_eq etm in
              let rth = BOUND_RULE bths rtm in
              let lth = GEN_REWRITE_RULE LAND_CONV [SYM eth] rth in
              let mth = prule lth in
              map (CONV_RULE(RAND_CONV NUM_REDUCE_CONV)) (CONJUNCTS mth)
          with Failure _ -> [] in
        DERIVE_BOUNDS_RULE (newths @ bths) oeths in
  DERIVE_BOUNDS_RULE;;
