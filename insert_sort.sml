(* insert_sort.sml — Standard ML (Poly/ML & CakeML compatible) verified insertion sort *)

structure InsertSort =
struct

  (* Core insertion into a sorted list using comparison function *)
  fun insBy (cmp : 'a * 'a -> order) (x : 'a) (l : 'a list) : 'a list =
    case l of
        [] => [x]
      | y :: ys =>
          (case cmp (x, y) of
               GREATER => y :: insBy cmp x ys
             | _ => x :: y :: ys)

  (* Insertion sort with explicit comparison function (stable) *)
  fun sortBy (cmp : 'a * 'a -> order) (l : 'a list) : 'a list =
    case l of
        [] => []
      | x :: xs => insBy cmp x (sortBy cmp xs)

  (* Integer insertion sort using Int.compare *)
  fun insert (x : int) (l : int list) : int list =
    insBy Int.compare x l

  fun insertion_sort (l : int list) : int list =
    sortBy Int.compare l

  (* Key-based insertion sort (stable) *)
  fun keySort (key : 'a -> int) (l : 'a list) : 'a list =
    let
      fun cmp (a, b) = Int.compare (key a, key b)
    in
      sortBy cmp l
    end

  (* Verification Helpers *)
  fun isSorted [] = true
    | isSorted [_] = true
    | isSorted (x :: (y :: ys)) =
        (x <= y) andalso isSorted (y :: ys)

  (* Test assertions *)
  fun assert (name : string) (cond : bool) =
    if cond then ()
    else (print ("FAIL: " ^ name ^ "\n"); OS.Process.exit OS.Process.failure)

  fun runTests () =
    let
      val s1 = insertion_sort []
      val _ = assert "empty" (s1 = [])

      val s2 = insertion_sort [42]
      val _ = assert "single" (s2 = [42])

      val s3 = insertion_sort [5, 4, 3, 2, 1]
      val _ = assert "reverse" (s3 = [1, 2, 3, 4, 5] andalso isSorted s3)

      val s4 = insertion_sort [3, 1, 4, 1, 5, 9, 2, 6, 5]
      val _ = assert "duplicates" (s4 = [1, 1, 2, 3, 4, 5, 5, 6, 9] andalso isSorted s4)

      (* Stability test: items with key and original index *)
      val items = [(2, "a"), (1, "b"), (2, "c"), (1, "d"), (2, "e")]
      val sortedItems = keySort #1 items
      val expected = [(1, "b"), (1, "d"), (2, "a"), (2, "c"), (2, "e")]
      val _ = assert "stability" (sortedItems = expected)
    in
      print "All SML InsertSort tests passed successfully.\n"
    end
end;

val _ = InsertSort.runTests ();
