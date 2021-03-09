(* 
                         CS 51 Problem Set 5
                Modules, Functors, and Priority Queues
             Ordered Collections and Binary Search Trees
 *)
   
(*======================================================================
Before working on this problem set, read the problem set 5 writeup in
the textbook. It provides context and crucial information for
completing the problems. In addition, make sure that you are familiar
with the problem set procedures in the document "Problem set
procedures for CS51". 

You are allowed (and encouraged) to work with a partner on this
problem set. You are also allowed to work alone, if you prefer. See
https://cs51.io/guides/procedures/pset-instructions/#working-with-a-partner
for further information on working with partners on problem sets.  
 *)
   
open Order

(*======================================================================
  Ordered collections 
 *)
   
module type ORDERED_COLLECTION =
sig
  exception Empty
  exception NotFound

  (* The type of an element in the collection *)
  type elt

  (* What this type actually looks like is left up to the particular
     implementation (the struct) *)
  type collection

  (* An empty collection *)
  val empty : collection

  (* Search a collection for the given value. *)
  val search : elt -> collection -> bool

  (* Insert elt into collection *)
  val insert : elt -> collection -> collection

  (* Delete the given value from a binary collection.
     May raise NotFound exception. *)
  val delete : elt -> collection -> collection

  (* Return the minimum value of a binary collection.
     May raise Empty exception *)
  val getmin : collection -> elt

  (* Return the maximum value of a binary collection.
     May raise Empty exception *)
  val getmax : collection -> elt

  (* Return a string of the given collection. *)
  val to_string : collection -> string
 
  (* Run invariant checks on the implementation of this binary collection.
     May raise Assert_failure exception *)
  val run_tests : unit -> unit
end

(*======================================================================
  Implementing ordered collections with binary search trees
 *)

(*......................................................................
Problem 1: Implementing ORDERED_COLLECTION with binary search trees

`BinSTree` is a *functor*, which takes an argument satisfying `Elt`, a
module that implements the `COMPARABLE` signature (from the `Order`
module). `BinSTree` ultimately must return a module that satisfies the
`ORDERED_COLLECTION` signature.

Now that we are passing in a `COMPARABLE` module, which separately
defines a type and comparison for that type, we can just implement
something matching `ORDERED_COLLECTION`'s signature in terms of that
type and comparison function, and can wait until later to actually say
what that type and comparison function are.

Here, you'll complete the implementation of the `BinSTree`
functor. Unlike a binary search tree you may have seen before, this
implementation keeps a list with each node in the tree that contains
inserted instances that are equal to each other (as per the comparison
function). For example, if the integer `3` is inserted into an `int
BinSTree` five times, then there will be a node with `[3; 3; 3; 3; 3]`
in the tree, and the node will only be removed after five deletions of
`3` (assuming no further intermediate insertions of `3`).
......................................................................*)

module BinSTree (Elt : COMPARABLE)
              : (ORDERED_COLLECTION with type elt = Elt.t) =
  struct
    (* Inside of here, you can use `Elt.t` to refer to the type
       defined in the `Elt` module (which matches the `COMPARABLE`
       signature), and `Elt.compare` to access the function that
       compares elements of type `Elt.t` *)
    exception Empty
    exception NotFound
    
    (* Grab the type of the tree element from the module `Elt` that's
       passed in.  This is the only place you explicitly need to use
       `Elt.t`; you should use `elt` everywhere else *)
    type elt = Elt.t
     
    (* The type for a collection, a binary search tree *)
    type tree =
      | Leaf
      | Branch of tree * elt list * tree
    type collection = tree 

    (* Representation of the empty collection *)
    let empty = Leaf
    
    (*..................................................................
    insert x t -- Inserts an element `x` into the tree `t`.  The left
    subtree of a given node should only have "smaller" elements than
    that node (as determined by the comparison function), while the
    right subtree should only have "larger". Remember that "equal"
    elements should all be stored in a list. *The most recently
    inserted elements should be at the front of the list so they can
    be preferentially found and deleted.* (This is important for later
    use in priority queues.)
    
    Hint: Use `Elt.compare`. See `delete` for inspiration.
    ..................................................................*)  
    let rec insert (x : elt) (t : tree) : tree =
       match t with
       | Leaf -> Branch (Leaf, [x], Leaf)
       | Branch (left_side, list, right_side) -> 
         let comparing = Elt.compare (List.hd list) x 
         in if comparing = Less then Branch (left_side, list, insert x right_side) 
            else if comparing = Greater then Branch (insert x left_side, list, right_side)
            else Branch (left_side, x :: list, right_side)

    (*..................................................................
    search x t -- Returns `true` if the element `x` is in tree `t`,
    `false` otherwise.  Hint: multiple values might compare `Equal` to
    `x`, but that doesn't necessarily mean that `x` itself is in the
    tree.
    ..................................................................*)
    let rec search (x : elt) (t : tree) : bool =
      match t with 
      | Leaf -> false
      | Branch (left_side, list, right_side) -> 
        if List.mem x list then true
        else search x left_side || search x right_side

    (* pull_min t -- A useful function for removing the node (list of
       elements) with the minimum value from a binary tree, returning
       that node and the tree with that node removed. Raises `Empty`
       if the tree is empty (and hence has no minimum element).
    
       The `pull_min` function is not defined in the signature
       `ORDERED_COLLECTION`.  When you're working on a structure that
       implements a signature like `ORDERED_COLLECTION`, you may write
       auxiliary functions for your implementation (such as
       `pull_min`) that are not defined in the signature.
    
       Note, however, that if a function `foo` *is* defined in a
       signature `BAR`, and you attempt to make a structure satisfying
       the signature `BAR`, then you *must* define the function `foo`
       in your structure.  Otherwise the compiler will complain that
       your structure does not, in fact, satisfy the signature `BAR`
       (but you claim that it does). So, if it's in the signature, it
       needs to be in the structure. But if it's in the structure, it
       doesn't necessarily need to show up in the signature. *)
    let rec pull_min (t : tree) : elt list * tree =
      match t with
      | Leaf -> raise Empty
      | Branch (Leaf, this, right) -> (this, right)
      | Branch (left, this, right) -> let min, left' = pull_min left in
                                      (min, Branch (left', this, right))
                
    (* delete x t -- Removes element `x` from tree `t`. If multiple
       elements are in the list, removes the one that was inserted
       *first*. *)
    let rec delete (x : elt) (t : tree) : tree =
      match t with
      | Leaf -> raise NotFound
      | Branch (left, this, right) ->
         (* Reverse the elements stored at this node so that we pop
            off the last element in the list *)
         match List.rev this with
         | [] -> failwith "delete: empty list as node" 
         | hd :: tl ->
            match Elt.compare x hd with
            | Less -> Branch (delete x left, this, right)
            | Greater -> Branch (left, this, delete x right)
            | Equal ->
               match tl with
               | _ :: _ -> Branch (left, List.rev tl, right)
               | [] ->
                  (* the list in the node is now empty, so we have to
                     remove the node from the tree. *)
                  match left, right with
                  | Leaf, _ -> right
                  | _, Leaf -> left
                  | _ -> let right_min, right' = pull_min right in
                         Branch (left, right_min, right')
    
    (*..................................................................
    getmin t -- Returns the minimum value of the tree `t`. If
    there are multiple minimum values, it should return the one that
    was inserted first (note that, even though the list might look
    like `[3; 3; 3; 3; 3]`, you should return the *last* `3` in the
    list. This is because we might pass in a module to this functor
    that defines a type and comparison function where each element in
    the list *is* distinct, but are `Equal` from the perspective of the
    comparison function (like `Order.IntStringCompare`).
    ..................................................................*)
    let getmin (t : tree) : elt =
      match pull_min t with
       | list, _ -> List.hd (List.rev list)

    (*..................................................................
    getmax t -- Returns the maximum value of the tree `t`. Similarly
    should return the last element in the matching list.

    The exception `Empty`, defined within this module, might come
    in handy.
    ..................................................................*)  
    let rec getmax (t : tree) : elt =
      match pull_min t with
       | list, Leaf -> List.hd (List.rev list)
       | _, rest_of_tree -> getmax rest_of_tree

    (* to_string t -- Generates a string representation of a binary
       search tree `t`, useful for testing! *)
    let to_string (t : tree) = 
      let list_to_string (lst: 'a list) =
        match lst with 
        | [] -> "[]"
        | [hd] -> "[" ^ (Elt.to_string hd) ^ "]"
        | hd :: tl -> "[" ^ List.fold_left
                              (fun a b -> a
                                          ^ "; "
                                          ^ (Elt.to_string b))
                              (Elt.to_string hd) tl ^ "]" in
      let rec to_string' (t: tree) = 
        match t with 
        | Leaf -> "Leaf"
        | Branch (l, m, r) ->
                 "Branch (" ^ (to_string' l) ^ ", "
                 ^ (list_to_string m) ^ ", " ^ (to_string' r) ^ ")" in
      to_string' t

    (* Functions for testing the implementation *)
    let test_insert () =
      let x = Elt.generate () in
      let t = insert x empty in
      assert (t = Branch(Leaf, [x], Leaf));
      let t = insert x t in
      assert (t = Branch(Leaf, [x;x], Leaf));
      let y = Elt.generate_gt x in
      let t = insert y t in
      assert (t = Branch(Leaf, [x;x], Branch(Leaf, [y], Leaf)));
      let z = Elt.generate_lt x in
      let t = insert z t in
      assert (t = Branch(Branch(Leaf, [z], Leaf), [x; x],
                         Branch(Leaf, [y], Leaf)));
      (* Can add further cases here *)
      ()
  
    (* Insert a bunch of elements, and test to make sure that we can
       search for all of them. *)
    let test_search () =
      let x = Elt.generate () in
      let t = insert x empty in
      assert (search x t);
      let order = [ true; false; true; true; true; false; false] in
      
      let full_tree, values_inserted =
        List.fold_right
          (fun current_order (tree_so_far, values_so_far) ->
           let prev_value =
             match values_so_far with
             | [] -> x
             | hd :: _ -> hd in
           let value =
             if current_order
             then Elt.generate_gt prev_value
             else Elt.generate_lt prev_value in
           insert value tree_so_far, value :: values_so_far)
          order (t, []) in
      
      List.iter (fun value -> assert (search value full_tree)) values_inserted
    
    (* None of these tests are particularly exhaustive.  For instance,
       we could try varying the order in which we insert values, and
       making sure that the result is still correct.  So, the strategy
       here is more to try to build up a reasonable degree of coverage
       across the various code-paths, rather than it is to test
       exhaustively that our code does the right thing on every single
       possible input.  *)
    let test_getmax () =
      let x = Elt.generate () in
      let x2 = Elt.generate_lt x in
      let x3 = Elt.generate_lt x2 in
      let x4 = Elt.generate_lt x3 in
      assert (getmax (insert x4 (insert x3 (insert x2 (insert x empty)))) = x)
       
    let test_getmin () =
      let x = Elt.generate () in
      let x2 = Elt.generate_gt x in
      let x3 = Elt.generate_gt x2 in
      let x4 = Elt.generate_gt x3 in
      assert (getmin (insert x2 (insert x4 (insert x (insert x3 empty)))) = x)
       
    let test_delete () =
      let x = Elt.generate () in
      let x2 = Elt.generate_lt x in
      let x3 = Elt.generate_lt x2 in
      let x4 = Elt.generate_lt x3 in
      let after_ins = insert x4 (insert x3 (insert x2 (insert x empty))) in
      assert (delete x (delete x4 (delete x3 (delete x2 after_ins))) = empty)
       
    let run_tests () =
      test_insert ();
      test_search ();
      test_getmax ();
      test_getmin ();
      test_delete ();
      ()
  
  end

(* Here is how you would define an integer binary search tree using
the `BinSTree` functor, which expects a module to be passed in as an
argument.  You should write tests using the `IntTree` module (or you
can give the module a different type), and you should use this call to
a functor as an example for how to test modules further down in the
pset. *)
    
module IntTree = BinSTree(IntCompare)
       
(* Please read the entirety of "tests.ml" for an explanation of how
testing works. *)
                         
(*======================================================================
Reflection on the problem set

After each problem set, we'll ask you to reflect on your experience.
We care about your responses and will use them to help guide us in
creating and improving future assignments.

........................................................................
Please give us an honest (if approximate) estimate of how long (in
minutes) this problem set (in total, not just this file) took you to
complete. (If you worked with a partner, we're asking for how much time
each of you (on average) spent on the problem set, not in total.)
......................................................................*)

let minutes_spent_on_pset () : int =
  360 ;;

(*......................................................................
It's worth reflecting on the work you did on this problem set. Where
did you run into problems and how did you end up resolving them? What
might you have done in retrospect that would have allowed you to
generate as good a submission in less time? Please provide us your
thoughts on these questions and any other reflections in the string
below.
......................................................................*)

let reflection () : string =
  "It was complicated at first but I read through the writeup and the other files
  thoroughly to get a really good understanding and it made more sense the second time.
  It still took long because I couldn;t manage to organize a partner in time. I didn't
  understand the testing at first but office hours helped with that immensely. " ;;
