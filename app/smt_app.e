note
	description: "Demo executable for simple_smt: proves a theorem and refutes a non-theorem"
	author: "Larry Rix"

class
	SMT_APP

create
	make

feature {NONE} -- Initialization

	make
			-- Demonstrate proving, refuting, and solving with Z3.
		local
			smt: SIMPLE_SMT
			x, y, z, zero, one: SMT_EXPR
		do
			create smt.make
			io.put_string ("simple_smt demo (Z3-backed)%N===========================%N%N")

			x := smt.int_const ("x")
			y := smt.int_const ("y")
			z := smt.int_const ("z")
			zero := smt.int_value (0)
			one := smt.int_value (1)

				-- Prove a contract fragment: x >= 0  implies  x + 1 > 0.
			io.put_string ("Theorem  x >= 0 -> x + 1 > 0 : ")
			report (smt.prove (x.at_least (zero).entails (x.plus (one).greater (zero))))

				-- Prove transitivity.
			io.put_string ("Theorem  x<y and y<z -> x<z : ")
			report (smt.prove (x.less (y).conjoined (y.less (z)).entails (x.less (z))))

				-- Refute a non-theorem and show the counter-model.
			io.put_string ("Non-theorem  x > 0 : ")
			report (smt.prove (x.greater (zero)))
			io.put_string ("  counter-model: " + smt.refutation (x.greater (zero)) + "%N")

				-- Solve a constraint and read the model.
			smt.assume (x.greater (smt.int_value (5)))
			smt.assume (x.less (smt.int_value (8)))
			io.put_string ("Solve  5 < x < 8 -> x = ")
			if smt.is_satisfiable then
				io.put_string (smt.model_value (x) + "%N")
			else
				io.put_string ("(unsat)%N")
			end
		end

feature {NONE} -- Implementation

	report (a_valid: BOOLEAN)
			-- Print PROVED / not valid.
		do
			if a_valid then
				io.put_string ("PROVED%N")
			else
				io.put_string ("not valid%N")
			end
		end

end
