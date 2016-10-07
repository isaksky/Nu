// Prime - A PRIMitivEs code library.
// Copyright (C) Bryan Edds, 2012-2016.

namespace Prime.Tests
open System
open Xunit
open FsCheck
open FsCheck.Xunit
open Prime
open System.Collections.Generic
open System.Diagnostics

module ResizeCloneOps = 
    let cloneAdd v (vs : List<_>) =
        seq {
            for x in vs do yield x
            yield v
        } |> List

    let cloneMap f (vs : List<'v>) : ResizeArray<'v> = Seq.map f vs |> ResizeArray

    let cloneFilter f (vs : List<_>) = Seq.filter f vs |> ResizeArray

    let cloneSet (idx : int) (v : 'v) (vs : List<_>) =
        let vs2 = List(vs.Capacity)
        vs2.AddRange(vs)
        vs2.[idx] <- v
        vs2

    let ofSeq xs =
        let ys = List()
        for x in xs do ys.Add(x)
        ys 

module ListCommands =
    let private eq testlist (list:List<_>) = 
        Seq.length testlist = list.Count &&
        Seq.forall2 (=) testlist list
    let private (==) (testlists: Ulist<int> list) (lists : List<int> list) =
        Seq.length testlists = List.length lists &&
        List.forall2 eq testlists lists
        
    let displayLists (testlists: Ulist<int> list) (lists : List<int> list) =
        let plists lists =
            let sb = Text.StringBuilder("[")
            for list in lists do
                sb.Append " [" |> ignore
                for i in list do
                    sb.Append(i.ToString()) |> ignore
                    sb.Append(' ') |> ignore
                sb.Append "] " |> ignore
            sb.Append(']') |> ignore
            sb.ToString()
        sprintf "Expected %s\nActual %s" (plists testlists) (plists lists)

    let mkCmd name applyToTest applyToModel =
        { new Command<Ulist<int> list, List<int> list>() with
            override __.RunActual testlists =
                match testlists with
                | h::tl -> (applyToTest h)::h::tl
                | _ -> failwithumf()
            override __.RunModel m =
                match m with
                | h::tl -> (applyToModel h)::h::tl
                | _ -> failwithumf() 
            override __.Post(testlists, lists) =
                testlists == lists |@ displayLists testlists lists
            override __.ToString() = name }

    let mapInc = mkCmd "mapInc" (Ulist.map ((+) 1)) (ResizeCloneOps.cloneMap ((+) 1))
    let even i = i % 2 = 0
    let filterEvens = mkCmd "filterEvens" (Ulist.filter even) (fun  b -> b) //(ResizeCloneOps.cloneFilter even) 
    
    let mkSpec initial = 
        { new ICommandGenerator<Ulist<int> list, List<int> list> with
            member __.InitialActual = [(Ulist.ofSeq initial)] 
            member __.InitialModel =
                [(ResizeCloneOps.ofSeq initial)]
            member __.Next m = Gen.elements [mapInc; filterEvens] }

module ListTests =
    type ListAction<'v> = 
        | AddLast of 'v
        | MapIncrementFn
        | FilterWithFn
        | SetNthToNth of int * int
        | FoldAddingLast

    /// Keeps a reference to all persistent collections returned after
    /// performing actions, and after they are all applied, checks
    /// that they equal what we would get from FSharp.Core.List
    let eqListsAfterSteps
        (list : 'v ResizeArray)
        (testlist : 'l)
        (actions : ListAction<'v> array)
        (addLast : 'v->'l->'l)
        (getNth : int->'l->'v)
        (setNth : int->'v->'l->'l)
        (incrf : 'v->'v)
        (mapf : ('v->'v)->'l->'l)
        (pred: 'v->bool)
        (filter: ('v->bool)->'l->'l)
        (eq : 'l->'v ResizeArray->bool)
        (mkSeed : unit->'v)
        (fold : ('v->'v->'v)->'v->'l->'v)
        (folder : 'v->'v->'v)
        (lookBackwards : bool) =

        let applyAction (list:'v ResizeArray) testlist action =
            match action with
            | ListAction.AddLast v ->
                (ResizeCloneOps.cloneAdd v list, addLast v testlist)
            | ListAction.MapIncrementFn ->
                (ResizeCloneOps.cloneMap incrf list, mapf incrf testlist)
            | ListAction.FilterWithFn ->
                (ResizeCloneOps.cloneFilter pred list, filter pred testlist)
            | ListAction.SetNthToNth(n1, n2) ->
                let len = list.Count
                if len > 0 then
                    let idx1, idx2 = n1 % len, n2 % len
                    let newlist = 
                        let v2 = Seq.item idx2 list
                        ResizeCloneOps.cloneSet idx1 v2 list
                    let test =
                        let v2 = getNth idx2 testlist
                        setNth idx1 v2 testlist
                    (newlist, test)
                else
                    (list, testlist)
            | ListAction.FoldAddingLast ->
                let newlist = ResizeCloneOps.cloneAdd (Seq.fold folder (mkSeed()) list) list
                let test = addLast (fold folder (mkSeed()) testlist) testlist
                (newlist, test)

        let (lists, testlists) =
            Array.fold
                (fun acc action ->
                    match acc with
                    | (fsmap :: fsmaps, testMap :: testMaps) ->
                        let (newF, newT) = applyAction fsmap testMap action
                        (newF :: fsmap :: fsmaps, newT :: testMap :: testMaps)
                    | _ -> failwithumf ())
                ([list], [testlist])
                actions

        let success = 
            if lookBackwards then
                List.forall2 eq testlists lists
            else
                eq (List.head testlists) (List.head lists)

        if not success then
            Trace.WriteLine "FAILURE:"
            List.iteri2 (fun i list testlist  ->
                if i > 0 then Trace.WriteLine (sprintf "After action %A" actions.[i-1])
                Trace.WriteLine (sprintf "list: %A\ntestlist: %A" list testlist))
                (List.rev lists)
                (List.rev testlists)
        success

    open FsCheck

    let getActionGen (pred: ListAction<int> -> bool) =
        Gen.map3 (fun i (PositiveInt j) (PositiveInt k) ->
            match i with
            | 0 -> ListAction.AddLast i 
            | 1 -> ListAction.FilterWithFn
            | 2 -> ListAction.FoldAddingLast
            | 3 -> ListAction.MapIncrementFn
            | 4 -> ListAction.SetNthToNth(j, k)
            | _ -> failwithumf())
            (Gen.choose(0, 4))
            (Arb.toGen ^ Arb.Default.PositiveInt())
            (Arb.toGen ^ Arb.Default.PositiveInt())
        |> Gen.filter pred
        |> Gen.arrayOf
        |> Arb.fromGen

    let getAllActionGen() = getActionGen (fun _ -> true)

    [<Property>]
    /// Proof of concept, we can delete this after we know test is correct
    let aryEqListsLookingBackwards (initialList : ResizeArray<int>) =
        let ary = Array.ofSeq initialList
        let eq (ary: int[]) (fslist: int ResizeArray) = List.ofSeq ary = List.ofSeq fslist
        let pred i = i % 2 = 0

        let add (v:int) (ary: int[]) =
            let ary2 = Array.zeroCreate (ary.Length + 1)
            Array.Copy(ary, ary2, ary.Length)
            ary2.[ary.Length] <- v
            ary2

        let get (i:int) (ary: int[]) = ary.[i]

        let set (i:int) (v:int) (ary: int[]) =
            let ary2 = Array.copy ary
            ary2.[i] <- v
            ary2

        Prop.forAll (getAllActionGen()) ^ fun actions ->
            eqListsAfterSteps initialList ary actions add get set ((+) 1) Array.map pred Array.filter eq (fun () -> 0) Array.fold (+) true

    let ulistEqLists (initialList : ResizeArray<int>) (actions : ListAction<int>[]) (lookBackwards : bool) =
        let testList = Ulist.addMany initialList (Ulist.makeEmpty(None))
        let eq (ulist : Ulist<_>) (fslist : _ ResizeArray) = List.ofSeq ulist = List.ofSeq fslist
        let pred i = i % 2 = 0
        eqListsAfterSteps initialList testList actions Ulist.add Ulist.get Ulist.set ((+) 1) Ulist.map pred Ulist.filter eq (fun () -> 0) Ulist.fold (+) lookBackwards

    [<Property>]
    let ulistEqList (initialList : ResizeArray<int>) =
        Prop.forAll (getAllActionGen()) ^ fun actions ->
            ulistEqLists initialList actions false 

    [<Property>]
    let ulistEqListsLookingBackwards (initialList : ResizeArray<int>) =
        Prop.forAll (getAllActionGen()) ^ (fun actions ->
            ulistEqLists initialList actions true)

    [<Property>]
    let ulistEqListsLookingBackwardsAddOnly (initialList : ResizeArray<int>) =
        let actionGen = getActionGen (function
            | ListAction.AddLast(_) -> true
            | _ -> false)

        Prop.forAll actionGen (fun actions ->
            ulistEqLists initialList actions true)

    [<Property>]
    let ulistEqListsLookingBackwardsAddSet (initialList : ResizeArray<int>) =
        let actionGen = getActionGen (function
            | ListAction.SetNthToNth(_,_)
            | ListAction.AddLast(_) -> true
            | _ -> false)

        Prop.forAll actionGen (fun actions ->
            ulistEqLists initialList actions true)

    [<Property>]
    let ulistEqListsLookingBackwardsMapFilter (initialList : ResizeArray<int>) =
        let actionGen = getActionGen (function
            | ListAction.MapIncrementFn(_)
            | ListAction.FilterWithFn -> true
            | _ -> false)

        Prop.forAll actionGen (fun actions ->
            ulistEqLists initialList actions true)

    [<Fact>]
    let ff () =
        let initialList = List()
        let spec = ListCommands.mkSpec initialList
        let prop = Command.toProperty spec
        Check.One (Config.Verbose, prop)