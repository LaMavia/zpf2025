{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Par
  ( happyError
  , myLexer
  , pProgram
  ) where

import Prelude

import qualified Abs
import Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap4 = HappyWrap4 ((Abs.BNFC'Position, Integer))
happyIn4 :: ((Abs.BNFC'Position, Integer)) -> (HappyAbsSyn )
happyIn4 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap4 x)
{-# INLINE happyIn4 #-}
happyOut4 :: (HappyAbsSyn ) -> HappyWrap4
happyOut4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut4 #-}
newtype HappyWrap5 = HappyWrap5 ((Abs.BNFC'Position, String))
happyIn5 :: ((Abs.BNFC'Position, String)) -> (HappyAbsSyn )
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap5 x)
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn ) -> HappyWrap5
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
newtype HappyWrap6 = HappyWrap6 ((Abs.BNFC'Position, Abs.UIdent))
happyIn6 :: ((Abs.BNFC'Position, Abs.UIdent)) -> (HappyAbsSyn )
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap6 x)
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn ) -> HappyWrap6
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
newtype HappyWrap7 = HappyWrap7 ((Abs.BNFC'Position, Abs.LIdent))
happyIn7 :: ((Abs.BNFC'Position, Abs.LIdent)) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap7 x)
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> HappyWrap7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
newtype HappyWrap8 = HappyWrap8 ((Abs.BNFC'Position, Abs.Program))
happyIn8 :: ((Abs.BNFC'Position, Abs.Program)) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap8 x)
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> HappyWrap8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
newtype HappyWrap9 = HappyWrap9 ((Abs.BNFC'Position, [Abs.Def]))
happyIn9 :: ((Abs.BNFC'Position, [Abs.Def])) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap9 x)
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> HappyWrap9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
newtype HappyWrap10 = HappyWrap10 ((Abs.BNFC'Position, Abs.Def))
happyIn10 :: ((Abs.BNFC'Position, Abs.Def)) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap10 x)
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> HappyWrap10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
newtype HappyWrap11 = HappyWrap11 ((Abs.BNFC'Position, Abs.TypeArg))
happyIn11 :: ((Abs.BNFC'Position, Abs.TypeArg)) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap11 x)
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> HappyWrap11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
newtype HappyWrap12 = HappyWrap12 ((Abs.BNFC'Position, [Abs.TypeArg]))
happyIn12 :: ((Abs.BNFC'Position, [Abs.TypeArg])) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap12 x)
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> HappyWrap12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
newtype HappyWrap13 = HappyWrap13 ((Abs.BNFC'Position, Abs.DeclHeader))
happyIn13 :: ((Abs.BNFC'Position, Abs.DeclHeader)) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap13 x)
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> HappyWrap13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
newtype HappyWrap14 = HappyWrap14 ((Abs.BNFC'Position, Abs.Stmt))
happyIn14 :: ((Abs.BNFC'Position, Abs.Stmt)) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap14 x)
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> HappyWrap14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
newtype HappyWrap15 = HappyWrap15 ((Abs.BNFC'Position, Abs.IExp))
happyIn15 :: ((Abs.BNFC'Position, Abs.IExp)) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap15 x)
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> HappyWrap15
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
newtype HappyWrap16 = HappyWrap16 ((Abs.BNFC'Position, Abs.IExp))
happyIn16 :: ((Abs.BNFC'Position, Abs.IExp)) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap16 x)
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> HappyWrap16
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
newtype HappyWrap17 = HappyWrap17 ((Abs.BNFC'Position, Abs.IExp))
happyIn17 :: ((Abs.BNFC'Position, Abs.IExp)) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap17 x)
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> HappyWrap17
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
newtype HappyWrap18 = HappyWrap18 ((Abs.BNFC'Position, Abs.IExp))
happyIn18 :: ((Abs.BNFC'Position, Abs.IExp)) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap18 x)
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> HappyWrap18
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
newtype HappyWrap19 = HappyWrap19 ((Abs.BNFC'Position, Abs.AddOp))
happyIn19 :: ((Abs.BNFC'Position, Abs.AddOp)) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap19 x)
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> HappyWrap19
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
newtype HappyWrap20 = HappyWrap20 ((Abs.BNFC'Position, Abs.MulOp))
happyIn20 :: ((Abs.BNFC'Position, Abs.MulOp)) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap20 x)
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> HappyWrap20
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
newtype HappyWrap21 = HappyWrap21 ((Abs.BNFC'Position, Abs.RelOp))
happyIn21 :: ((Abs.BNFC'Position, Abs.RelOp)) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap21 x)
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> HappyWrap21
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
newtype HappyWrap22 = HappyWrap22 ((Abs.BNFC'Position, Abs.Term))
happyIn22 :: ((Abs.BNFC'Position, Abs.Term)) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap22 x)
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> HappyWrap22
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
newtype HappyWrap23 = HappyWrap23 ((Abs.BNFC'Position, [Abs.Term]))
happyIn23 :: ((Abs.BNFC'Position, [Abs.Term])) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap23 x)
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> HappyWrap23
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
newtype HappyWrap24 = HappyWrap24 ((Abs.BNFC'Position, [Abs.Stmt]))
happyIn24 :: ((Abs.BNFC'Position, [Abs.Stmt])) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap24 x)
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> HappyWrap24
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x00\x02\x00\x20\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x80\x10\x00\x83\x06\x00\x00\x00\x20\x00\x00\x02\x00\x00\x20\x00\x00\xe5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x80\x00\x00\x94\x03\x00\x00\x40\x00\x00\xca\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x40\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x24\x08\x00\x00\x00\x00\x00\xa1\x60\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x21\x00\x00\x05\x00\x00\x80\x00\x00\x80\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\xc0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x22\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x04\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\x02\x00\x00\x00\x00\x00\x08\x01\x00\x28\x00\x00\x00\x84\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x42\x00\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x04\xc0\xa0\x01\x00\x00\x10\x00\x80\x72\x00\x00\x00\x08\x00\x40\x39\x00\x00\x00\x84\x00\x00\x14\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\xca\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x80\x72\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x00\x00\x48\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x40\x00\x00\x00\x00\x00\x00\x10\x18\x00\x00\x00\x00\x00\x08\x0c\x00\x00\x00\x00\x00\x04\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","Integer","String","UIdent","LIdent","Program","ListDef","Def","TypeArg","ListTypeArg","DeclHeader","Stmt","IExp3","IExp2","IExp1","IExp","AddOp","MulOp","RelOp","Term","ListTerm","ListStmt","'!='","'%'","'('","')'","'*'","'+'","','","'-'","'.'","'.decl'","'/'","':'","':-'","'<'","'<='","'='","'=='","'>'","'>='","'False'","'True'","'['","']'","'_'","'is'","'|'","L_integ","L_quoted","L_UIdent","L_LIdent","%eof"]
        bit_start = st Prelude.* 55
        bit_end = (st Prelude.+ 1) Prelude.* 55
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..54]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\xf8\xff\xe8\xff\x00\x00\x01\x00\xf0\xff\x00\x00\x33\x00\x20\x00\xf9\xff\x00\x00\x4f\x00\xfe\xff\xf8\xff\x02\x00\x00\x00\x00\x00\x00\x00\x43\x00\x6a\x00\x02\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\xff\x55\x00\x6e\x00\x00\x00\x00\x00\x09\x00\x54\x00\x00\x00\x05\x00\x06\x00\x00\x00\x00\x00\x56\x00\x00\x00\x00\x00\x5d\x00\x6d\x00\x56\x00\x00\x00\x00\x00\x7c\x00\x05\x00\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00\xfe\xff\x02\x00\x02\x00\x05\x00\x72\x00\x92\x00\x00\x00\x02\x00\x00\x00\x02\x00\x00\x00\x22\x00\x00\x00\xa9\x00\x00\x00\x00\x00\x22\x00\x09\x00\x00\x00\x0e\x00\x56\x00\x56\x00\x56\x00\x00\x00\xaa\x00\xac\x00\x00\x00\x00\x00\xad\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x90\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa2\x00\x00\x00\x00\x00\x24\x00\x58\x00\x39\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x47\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9c\x00\x60\x00\x00\x00\x6b\x00\x0a\x00\x00\x00\x00\x00\x95\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa8\x00\x00\x00\x00\x00\xa3\x00\x83\x00\x70\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x86\x00\x00\x00\x00\x00\x00\x00\x29\x00\x41\x00\x4d\x00\x7f\x00\x00\x00\x00\x00\x00\x00\x44\x00\x00\x00\x68\x00\x00\x00\xa3\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa3\x00\xa4\x00\x00\x00\x00\x00\x98\x00\x9f\x00\xa1\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\x00\x00\xfe\xff\x00\x00\x00\x00\xfa\xff\x00\x00\xf6\xff\x00\x00\xfb\xff\x00\x00\xc9\xff\xf9\xff\xcc\xff\xd1\xff\xd2\xff\xd0\xff\xcb\xff\x00\x00\x00\x00\xcc\xff\xcf\xff\xfd\xff\xfc\xff\xf8\xff\xe5\xff\xe6\xff\x00\x00\xc8\xff\xe2\xff\xe0\xff\xde\xff\x00\x00\xf5\xff\x00\x00\x00\x00\xeb\xff\xec\xff\xf0\xff\xf4\xff\xf3\xff\xef\xff\x00\x00\x00\x00\xe6\xff\xe3\xff\x00\x00\x00\x00\x00\x00\xd3\xff\xdd\xff\xdc\xff\xd8\xff\xd7\xff\xd4\xff\xd6\xff\xd5\xff\x00\x00\xd9\xff\xdb\xff\xda\xff\xc9\xff\xcc\xff\x00\x00\x00\x00\x00\x00\x00\x00\xed\xff\xcc\xff\xca\xff\x00\x00\xce\xff\xe8\xff\xe9\xff\x00\x00\xc7\xff\xe1\xff\xe7\xff\xdf\xff\xe4\xff\x00\x00\xf0\xff\xf0\xff\xf0\xff\xee\xff\x00\x00\x00\x00\xf2\xff\xea\xff\x00\x00\xcd\xff\xf7\xff\xf1\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x03\x00\x0a\x00\x1b\x00\x03\x00\x03\x00\x08\x00\x10\x00\x03\x00\x03\x00\x00\x00\x02\x00\x02\x00\x08\x00\x05\x00\x1f\x00\x19\x00\x03\x00\x14\x00\x15\x00\x0b\x00\x0b\x00\x1e\x00\x1e\x00\x16\x00\x1b\x00\x18\x00\x1d\x00\x1e\x00\x1b\x00\x1c\x00\x1d\x00\x1b\x00\x1b\x00\x1d\x00\x1d\x00\x00\x00\x17\x00\x02\x00\x03\x00\x06\x00\x00\x00\x08\x00\x02\x00\x03\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x14\x00\x00\x00\x01\x00\x02\x00\x09\x00\x14\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\x00\x00\x01\x00\x02\x00\x07\x00\x12\x00\x13\x00\x00\x00\x01\x00\x02\x00\x12\x00\x13\x00\x03\x00\x12\x00\x13\x00\x01\x00\x12\x00\x13\x00\x03\x00\x12\x00\x06\x00\x03\x00\x08\x00\x05\x00\x06\x00\x12\x00\x03\x00\x09\x00\x0e\x00\x0f\x00\x07\x00\x11\x00\x12\x00\x13\x00\x00\x00\x01\x00\x02\x00\x00\x00\x16\x00\x02\x00\x04\x00\x0f\x00\x00\x00\x11\x00\x02\x00\x1d\x00\x1e\x00\x07\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x12\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x00\x00\x04\x00\x02\x00\x06\x00\x00\x00\x08\x00\x02\x00\x00\x00\x1a\x00\x02\x00\x17\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0b\x00\x0c\x00\x0d\x00\x0b\x00\x0c\x00\x03\x00\x04\x00\x05\x00\x06\x00\x02\x00\x03\x00\x09\x00\x02\x00\x03\x00\x07\x00\x08\x00\x0c\x00\x07\x00\x08\x00\x02\x00\x03\x00\x02\x00\x03\x00\x03\x00\x07\x00\x08\x00\x07\x00\x08\x00\x02\x00\x03\x00\x10\x00\x04\x00\x04\x00\x07\x00\x04\x00\x04\x00\x0f\x00\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x23\x00\x09\x00\x03\x00\x0e\x00\x14\x00\x24\x00\x40\x00\x23\x00\x23\x00\x19\x00\x3b\x00\x2c\x00\x24\x00\x3c\x00\xff\xff\x41\x00\x53\x00\x25\x00\x26\x00\x3d\x00\x2d\x00\x0a\x00\x0a\x00\x15\x00\x03\x00\x16\x00\x18\x00\x0a\x00\x03\x00\x17\x00\x18\x00\x03\x00\x03\x00\x18\x00\x18\x00\x19\x00\x58\x00\x1a\x00\x1b\x00\x33\x00\x19\x00\x34\x00\x1a\x00\x1b\x00\x0c\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x0e\x00\x0f\x00\x10\x00\x0d\x00\x4b\x00\x0e\x00\x0f\x00\x10\x00\x0e\x00\x0f\x00\x10\x00\x0e\x00\x0f\x00\x10\x00\x0e\x00\x0f\x00\x10\x00\x45\x00\x11\x00\x12\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x41\x00\x27\x00\x11\x00\x4a\x00\x32\x00\x11\x00\x45\x00\x3f\x00\x42\x00\x33\x00\x03\x00\x34\x00\x18\x00\x06\x00\x49\x00\x53\x00\x07\x00\x35\x00\x36\x00\x54\x00\x37\x00\x38\x00\x39\x00\x0e\x00\x0f\x00\x10\x00\x19\x00\x2c\x00\x2c\x00\x44\x00\x2f\x00\x19\x00\x30\x00\x2c\x00\x18\x00\x0a\x00\x3e\x00\x1d\x00\x1e\x00\x1f\x00\x2e\x00\x59\x00\x1d\x00\x1e\x00\x1f\x00\x4d\x00\x19\x00\x50\x00\x2c\x00\x33\x00\x19\x00\x34\x00\x2c\x00\x19\x00\x52\x00\x2c\x00\x48\x00\x1d\x00\x1e\x00\x1f\x00\x48\x00\x1d\x00\x1e\x00\x4e\x00\x1d\x00\x4c\x00\x03\x00\x04\x00\x05\x00\x06\x00\x27\x00\x28\x00\x07\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x47\x00\x29\x00\x56\x00\x27\x00\x28\x00\x27\x00\x28\x00\x0a\x00\x29\x00\x55\x00\x29\x00\x54\x00\x27\x00\x28\x00\x39\x00\x59\x00\x5d\x00\x50\x00\x5c\x00\x5b\x00\x2f\x00\x00\x00\x39\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (1, 56) [
	(1 , happyReduce_1),
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56)
	]

happy_n_terms = 32 :: Prelude.Int
happy_n_nonterms = 21 :: Prelude.Int

happyReduce_1 = happySpecReduce_1  0# happyReduction_1
happyReduction_1 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn4
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), (read (tokenText happy_var_1)) :: Integer)
	)}

happyReduce_2 = happySpecReduce_1  1# happyReduction_2
happyReduction_2 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn5
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), ((\(PT _ (TL s)) -> s) happy_var_1))
	)}

happyReduce_3 = happySpecReduce_1  2# happyReduction_3
happyReduction_3 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn6
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.UIdent (tokenText happy_var_1))
	)}

happyReduce_4 = happySpecReduce_1  3# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn7
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.LIdent (tokenText happy_var_1))
	)}

happyReduce_5 = happySpecReduce_1  4# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	happyIn8
		 ((fst happy_var_1, Abs.Program (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_6 = happySpecReduce_2  5# happyReduction_6
happyReduction_6 happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	happyIn9
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)}

happyReduce_7 = happySpecReduce_3  5# happyReduction_7
happyReduction_7 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	case happyOut9 happy_x_3 of { (HappyWrap9 happy_var_3) -> 
	happyIn9
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_8 = happyReduce 7# 6# happyReduction_8
happyReduction_8 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut7 happy_x_2 of { (HappyWrap7 happy_var_2) -> 
	case happyOut12 happy_x_4 of { (HappyWrap12 happy_var_4) -> 
	case happyOut12 happy_x_6 of { (HappyWrap12 happy_var_6) -> 
	happyIn10
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.TDef (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest}}}}

happyReduce_9 = happySpecReduce_1  6# happyReduction_9
happyReduction_9 happy_x_1
	 =  case happyOut13 happy_x_1 of { (HappyWrap13 happy_var_1) -> 
	happyIn10
		 ((fst happy_var_1, Abs.DFact (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_10 = happySpecReduce_3  6# happyReduction_10
happyReduction_10 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { (HappyWrap13 happy_var_1) -> 
	case happyOut24 happy_x_3 of { (HappyWrap24 happy_var_3) -> 
	happyIn10
		 ((fst happy_var_1, Abs.DRule (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_11 = happySpecReduce_1  7# happyReduction_11
happyReduction_11 happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	happyIn11
		 ((fst happy_var_1, Abs.TALit (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_12 = happySpecReduce_1  7# happyReduction_12
happyReduction_12 happy_x_1
	 =  case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	happyIn11
		 ((fst happy_var_1, Abs.TAGen (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_13 = happySpecReduce_3  7# happyReduction_13
happyReduction_13 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut11 happy_x_2 of { (HappyWrap11 happy_var_2) -> 
	happyIn11
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.TAList (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)}}

happyReduce_14 = happyReduce 4# 7# happyReduction_14
happyReduction_14 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	case happyOut12 happy_x_3 of { (HappyWrap12 happy_var_3) -> 
	happyIn11
		 ((fst happy_var_1, Abs.TAApp (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	) `HappyStk` happyRest}}

happyReduce_15 = happySpecReduce_0  8# happyReduction_15
happyReduction_15  =  happyIn12
		 ((Abs.BNFC'NoPosition, [])
	)

happyReduce_16 = happySpecReduce_1  8# happyReduction_16
happyReduction_16 happy_x_1
	 =  case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	happyIn12
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)}

happyReduce_17 = happySpecReduce_3  8# happyReduction_17
happyReduction_17 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	case happyOut12 happy_x_3 of { (HappyWrap12 happy_var_3) -> 
	happyIn12
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_18 = happyReduce 4# 9# happyReduction_18
happyReduction_18 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	case happyOut23 happy_x_3 of { (HappyWrap23 happy_var_3) -> 
	happyIn13
		 ((fst happy_var_1, Abs.DHeader (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	) `HappyStk` happyRest}}

happyReduce_19 = happySpecReduce_1  10# happyReduction_19
happyReduction_19 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn14
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.STrue (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_20 = happySpecReduce_1  10# happyReduction_20
happyReduction_20 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn14
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.SFalse (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_21 = happyReduce 4# 10# happyReduction_21
happyReduction_21 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	case happyOut23 happy_x_3 of { (HappyWrap23 happy_var_3) -> 
	happyIn14
		 ((fst happy_var_1, Abs.SCall (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	) `HappyStk` happyRest}}

happyReduce_22 = happySpecReduce_3  10# happyReduction_22
happyReduction_22 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut22 happy_x_3 of { (HappyWrap22 happy_var_3) -> 
	happyIn14
		 ((fst happy_var_1, Abs.SAss (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_23 = happySpecReduce_3  10# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn14
		 ((fst happy_var_1, Abs.SIs (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_24 = happySpecReduce_3  10# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut21 happy_x_2 of { (HappyWrap21 happy_var_2) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn14
		 ((fst happy_var_1, Abs.SRel (fst happy_var_1) (snd happy_var_1) (snd happy_var_2) (snd happy_var_3))
	)}}}

happyReduce_25 = happySpecReduce_1  11# happyReduction_25
happyReduction_25 happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	happyIn15
		 ((fst happy_var_1, Abs.IEVar (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_26 = happySpecReduce_1  11# happyReduction_26
happyReduction_26 happy_x_1
	 =  case happyOut4 happy_x_1 of { (HappyWrap4 happy_var_1) -> 
	happyIn15
		 ((fst happy_var_1, Abs.IELit (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_27 = happySpecReduce_3  11# happyReduction_27
happyReduction_27 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	happyIn15
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)}}

happyReduce_28 = happySpecReduce_2  12# happyReduction_28
happyReduction_28 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut15 happy_x_2 of { (HappyWrap15 happy_var_2) -> 
	happyIn16
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.IENeg (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)}}

happyReduce_29 = happySpecReduce_1  12# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	happyIn16
		 ((fst happy_var_1, (snd happy_var_1))
	)}

happyReduce_30 = happySpecReduce_3  13# happyReduction_30
happyReduction_30 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { (HappyWrap17 happy_var_1) -> 
	case happyOut20 happy_x_2 of { (HappyWrap20 happy_var_2) -> 
	case happyOut16 happy_x_3 of { (HappyWrap16 happy_var_3) -> 
	happyIn17
		 ((fst happy_var_1, Abs.IEMul (fst happy_var_1) (snd happy_var_1) (snd happy_var_2) (snd happy_var_3))
	)}}}

happyReduce_31 = happySpecReduce_1  13# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut16 happy_x_1 of { (HappyWrap16 happy_var_1) -> 
	happyIn17
		 ((fst happy_var_1, (snd happy_var_1))
	)}

happyReduce_32 = happySpecReduce_3  14# happyReduction_32
happyReduction_32 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut19 happy_x_2 of { (HappyWrap19 happy_var_2) -> 
	case happyOut17 happy_x_3 of { (HappyWrap17 happy_var_3) -> 
	happyIn18
		 ((fst happy_var_1, Abs.IEAdd (fst happy_var_1) (snd happy_var_1) (snd happy_var_2) (snd happy_var_3))
	)}}}

happyReduce_33 = happySpecReduce_1  14# happyReduction_33
happyReduction_33 happy_x_1
	 =  case happyOut17 happy_x_1 of { (HappyWrap17 happy_var_1) -> 
	happyIn18
		 ((fst happy_var_1, (snd happy_var_1))
	)}

happyReduce_34 = happySpecReduce_1  15# happyReduction_34
happyReduction_34 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn19
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.Plus (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_35 = happySpecReduce_1  15# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn19
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.Minus (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_36 = happySpecReduce_1  16# happyReduction_36
happyReduction_36 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn20
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.Times (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_37 = happySpecReduce_1  16# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn20
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.Div (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_38 = happySpecReduce_1  16# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn20
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.Mod (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_39 = happySpecReduce_1  17# happyReduction_39
happyReduction_39 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.LTH (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_40 = happySpecReduce_1  17# happyReduction_40
happyReduction_40 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.LE (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_41 = happySpecReduce_1  17# happyReduction_41
happyReduction_41 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.GTH (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_42 = happySpecReduce_1  17# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.GE (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_43 = happySpecReduce_1  17# happyReduction_43
happyReduction_43 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.EQU (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_44 = happySpecReduce_1  17# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.NE (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_45 = happySpecReduce_1  18# happyReduction_45
happyReduction_45 happy_x_1
	 =  case happyOut5 happy_x_1 of { (HappyWrap5 happy_var_1) -> 
	happyIn22
		 ((fst happy_var_1, Abs.TStr (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_46 = happySpecReduce_1  18# happyReduction_46
happyReduction_46 happy_x_1
	 =  case happyOut4 happy_x_1 of { (HappyWrap4 happy_var_1) -> 
	happyIn22
		 ((fst happy_var_1, Abs.TInt (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_47 = happySpecReduce_1  18# happyReduction_47
happyReduction_47 happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	happyIn22
		 ((fst happy_var_1, Abs.TVar (fst happy_var_1) (snd happy_var_1))
	)}

happyReduce_48 = happySpecReduce_1  18# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn22
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.TIgnore (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)}

happyReduce_49 = happySpecReduce_3  18# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_2 of { (HappyWrap23 happy_var_2) -> 
	happyIn22
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.TList (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)}}

happyReduce_50 = happyReduce 5# 18# happyReduction_50
happyReduction_50 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut22 happy_x_2 of { (HappyWrap22 happy_var_2) -> 
	case happyOut22 happy_x_4 of { (HappyWrap22 happy_var_4) -> 
	happyIn22
		 ((uncurry Abs.BNFC'Position (tokenLineCol happy_var_1), Abs.TCons (uncurry Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest}}}

happyReduce_51 = happySpecReduce_0  19# happyReduction_51
happyReduction_51  =  happyIn23
		 ((Abs.BNFC'NoPosition, [])
	)

happyReduce_52 = happySpecReduce_1  19# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut22 happy_x_1 of { (HappyWrap22 happy_var_1) -> 
	happyIn23
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)}

happyReduce_53 = happySpecReduce_3  19# happyReduction_53
happyReduction_53 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { (HappyWrap22 happy_var_1) -> 
	case happyOut23 happy_x_3 of { (HappyWrap23 happy_var_3) -> 
	happyIn23
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)}}

happyReduce_54 = happySpecReduce_0  20# happyReduction_54
happyReduction_54  =  happyIn24
		 ((Abs.BNFC'NoPosition, [])
	)

happyReduce_55 = happySpecReduce_1  20# happyReduction_55
happyReduction_55 happy_x_1
	 =  case happyOut14 happy_x_1 of { (HappyWrap14 happy_var_1) -> 
	happyIn24
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)}

happyReduce_56 = happySpecReduce_3  20# happyReduction_56
happyReduction_56 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_1 of { (HappyWrap14 happy_var_1) -> 
	case happyOut24 happy_x_3 of { (HappyWrap24 happy_var_3) -> 
	happyIn24
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)}}

happyNewToken action sts stk [] =
	happyDoAction 31# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TI _) -> cont 27#;
	PT _ (TL _) -> cont 28#;
	PT _ (T_UIdent _) -> cont 29#;
	PT _ (T_LIdent _) -> cont 30#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 31# tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (let {(HappyWrap8 x') = happyOut8 x} in x'))

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Abs.Program
pProgram = fmap snd . pProgram_internal
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Prelude.Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Prelude.Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Prelude.Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



















data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Prelude.Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else Prelude.False
         action
          | check     = indexShortOffAddr happyTable off_i
          | Prelude.otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `Prelude.mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)













-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ((Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
