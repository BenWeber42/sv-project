note
    description: "Verify the features by adding the missing loop invariants and postconditions."

class
    SV_AUTOPROOF

feature

    lst: SIMPLE_ARRAY [INTEGER]

feature

    wipe (x: SIMPLE_ARRAY [INTEGER])
        note
        	explicit: wrapping
		require
			x /= Void
			modify (x)
		local
			k: INTEGER
		do
			from
				k := 1
			invariant
				x.is_wrapped
				x.count = x.count.old_
    		    across 1 |..| (k - 1) as i all x.sequence [i.item] = 0 end
			until
				k > x.count
			loop
				x [k] := 0
				k := k + 1
			end
		ensure
			x.count = old x.count
			across 1 |..| x.count as i all x.sequence [i.item] = 0 end
		end


	mod_three (a, b: SIMPLE_ARRAY [INTEGER])
		note
			explicit: wrapping
		require
			a /= Void
			b /= Void
			a /= b
			a.count = b.count
			a.count > 0
			modify (a, b)
		local
			k: INTEGER
		do
			wipe (a)
			wipe (b)
			from
				k := 1
			invariant
				a.is_wrapped and b.is_wrapped
				a.count = a.count.old_
                a.count = b.count
                across 1 |..| a.count as i all a.sequence[i.item] = 0 end
    		    across 1 |..| (k - 1) as i all (i.item \\ 3 = 0) implies b.sequence [i.item] = 1 end
			until
				k > a.count
			loop
				if k \\ 3 = 0 then
					b [k] := a[k] + 1
				end
				k := k + 1
			end
		ensure
			across 1 |..| b.count as i all (i.item \\ 3 = 0) implies b.sequence [i.item] = 1 end
		end


feature

	swap (x, y: INTEGER)
		note
			explicit: wrapping
		require
			lst.is_wrapped
			1 <= x and x <= lst.count
			1 <= y and y <= lst.count
			modify (lst)
		local
			z: INTEGER
		do
			z := lst [x]
			lst [x] := lst [y]
			lst [y] := z
		ensure
			lst.is_wrapped
			lst.count = old lst.count
			across 1 |..| lst.count as i all i.item /= x and i.item /= y implies lst.sequence [i.item] = (old lst.sequence) [i.item] end
			lst.sequence [x] = (old lst.sequence) [y]
			lst.sequence [y] = (old lst.sequence) [x]
		end


	swapper
		note
			explicit: wrapping
		require
			lst.is_wrapped
			lst /= Void
			modify (lst)
		local
			x, y: INTEGER
		do
			from
				x := 1
				y := lst.count
			invariant
				lst.is_wrapped
				lst.sequence.count = lst.sequence.old_.count
                1 <= x
                y <= lst.count
                y = lst.count - x + 1
                across 1 |..| (x - 1) as i all lst.sequence [i.item] = lst.sequence.old_ [lst.count - i.item + 1] end
                across (y + 1) |..| lst.count as i all lst.sequence [i.item] = lst.sequence.old_ [lst.count - i.item + 1] end
                across x |..| y as i all lst.sequence [i.item] = lst.sequence.old_ [i.item] end
			until
				y <= x
			loop
				swap (x, y)
				x := x + 1
				y := y - 1
			end
		ensure
			lst.is_wrapped
			lst.sequence.count = (old lst.sequence).count
			across 1 |..| lst.count as i all lst.sequence [i.item] = (old lst.sequence) [lst.count - i.item + 1] end
		end


feature

	search (v: INTEGER): BOOLEAN
    	note
			status: impure
		require
			lst.is_wrapped
			lst /= Void
		local
			k: INTEGER
		do
			from
				k := lst.count
				Result := False
			invariant
                k <= lst. count
                Result implies lst.sequence[k] = v
                not Result implies across (k + 1) |..| lst.count as i all lst.sequence [i.item] /= v end
			until
				Result or k < 1
			loop
				if lst [k] = v then
					Result := True
				else
					k := k - 1
				end
			variant
				k - if Result then 1 else 0 end
			end
		ensure
            unmodified_count: lst.count = old lst.count
            unmodified_lst: across 1 |..| lst.count as i all lst.sequence [i.item] = (old lst.sequence) [i.item] end
            unmodified_v: v = old v
    		correctness: lst.sequence.has (v) = Result
		end


feature

	xx, zz: INTEGER


	prod_sum (y: INTEGER)
		require
			xx >= 0
			zz >= 0
			y > 0
		do
			from
				zz := 0
			invariant
				is_open
				inv
    		    zz * y + xx = xx.old_
			until
				xx < y
			loop
				zz := zz + 1
				xx := xx - y
			end
		ensure
			zz * y + xx = old xx
		end


feature

	paly (a: SIMPLE_ARRAY [INTEGER]): BOOLEAN
		note
			explicit: wrapping
		require
			a /= Void
		local
			x, y: INTEGER
		do
			from
				x := 1
				y := a.count
				Result := True
			invariant
                1 <= x
                y <= a.count
                y = a.count - x + 1
                Result = across 1 |..| (x - 1) as i all a.sequence [i.item] = a.sequence [a.count - i.item + 1] end
                not Result implies a.sequence [x - 1] /= a.sequence [y + 1]
			until
				x >= y or not Result
			loop
				if a [x] /= a [y] then
					Result := False
				end
				x := x + 1
				y := y - 1
			variant
				y - x
			end
		ensure
            Result = across 1 |..| a.count as i all a.sequence [i.item] = a.sequence [a.count - i.item + 1] end
            a.count = (old a).count
            across 1 |..| a.count as i all a.sequence [i.item] = (old a).sequence [i.item] end
		end


end
