(* binary_insert_sort.sml -- Standard ML (Poly/ML and CakeML compatible) binary insertion sort *)

structure BinaryInsertSort =
struct

  (* Bisect right: finds insertion index in arr[0 .. len-1] such that duplicates are placed after existing equals *)
  fun bisectRight (cmp : 'a * 'a -> order) (arr : 'a array) (len : int) (x : 'a) : int =
    let
      fun loop (low : int, high : int) : int =
        if low >= high then low
        else
          let
            val mid = low + (high - low) div 2
            val midElem = Array.sub (arr, mid)
          in
            case cmp (x, midElem) of
                LESS => loop (low, mid)
              | _ => loop (mid + 1, high)
          end
    in
      loop (0, len)
    end

  (* Shift elements in arr from pos up to len-1 one position to the right, then insert x at pos *)
  fun shiftAndInsert (arr : 'a array) (pos : int) (len : int) (x : 'a) : unit =
    let
      fun shift (j : int) : unit =
        if j < pos then ()
        else
          let
            val v = Array.sub (arr, j)
            val _ = Array.update (arr, j + 1, v)
          in
            shift (j - 1)
          end
      val _ = shift (len - 1)
      val _ = Array.update (arr, pos, x)
    in
      ()
    end

  (* In-place binary insertion sort on an array *)
  fun sortArray (cmp : 'a * 'a -> order) (arr : 'a array) : unit =
    let
      val n = Array.length arr
      fun step (i : int) : unit =
        if i >= n then ()
        else
          let
            val x = Array.sub (arr, i)
            val pos = bisectRight cmp arr i x
            val _ = shiftAndInsert arr pos i x
          in
            step (i + 1)
          end
    in
      step 1
    end

  (* Convert array to list *)
  fun arrayToList (arr : 'a array) : 'a list =
    Array.foldr (fn (x, acc) => x :: acc) [] arr

  (* Stable binary insertion sort on lists with custom comparator *)
  fun sortBy (cmp : 'a * 'a -> order) (l : 'a list) : 'a list =
    case l of
        [] => []
      | [_] => l
      | _ =>
          let
            val arr = Array.fromList l
            val _ = sortArray cmp arr
          in
            arrayToList arr
          end

  (* Sort with comparison counting *)
  fun sortCounted (cmp : 'a * 'a -> order) (l : 'a list) : 'a list * int =
    let
      val count = ref 0
      fun countedCmp (a, b) =
        let
          val _ = count := (!count) + 1
        in
          cmp (a, b)
        end
      val res = sortBy countedCmp l
    in
      (res, !count)
    end

  (* Integer binary insertion sort *)
  fun insertion_sort (l : int list) : int list =
    sortBy Int.compare l

  (* Key-based binary insertion sort (stable) *)
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

      (* Stability test: items with key and original tag *)
      val items = [(2, "a"), (1, "b"), (2, "c"), (1, "d"), (2, "e")]
      val sortedItems = keySort #1 items
      val expected = [(1, "b"), (1, "d"), (2, "a"), (2, "c"), (2, "e")]
      val _ = assert "stability" (sortedItems = expected)

      (* Comparison count test: 10 elements takes at most 10 * ceil(log2 10) = 40 comparisons *)
      val (s5, cmpCount) = sortCounted Int.compare [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
      val _ = assert "sorted_counted" (s5 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
      val _ = assert "comparison_count" (cmpCount <= 35)
    in
      print "All SML BinaryInsertSort tests passed successfully.\n"
    end
end;

val _ = BinaryInsertSort.runTests ();
