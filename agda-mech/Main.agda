{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)

module Main (extensionality : Ext.Extensionality lzero lzero) where

open import Filling extensionality
open import Confluence extensionality
