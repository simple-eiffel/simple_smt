note
	description: "[
		Owns a Z3 configuration and context, and is the factory for sorts,
		expressions, and solvers. All inline-C externals over Z3's C API live
		here (stateless calls that take the context pointer); sibling wrapper
		classes call them through this object.

		Uses Z3_mk_context: AST nodes live for the context's lifetime, so no
		per-AST reference counting is needed. Solvers and models are ref-counted.
	]"
	author: "Larry Rix"

class
	SMT_CONTEXT

create
	make

feature {NONE} -- Initialization

	make
			-- Create a fresh Z3 configuration and context.
		do
			config := c_mk_config
			context := c_mk_context (config)
		ensure
			context_attached: context /= default_pointer
		end

feature -- Access

	context: POINTER
			-- The Z3_context handle.

	int_sort: POINTER
			-- Cached integer sort.
		do
			if internal_int_sort = default_pointer then
				internal_int_sort := c_mk_int_sort (context)
			end
			Result := internal_int_sort
		end

	bool_sort: POINTER
			-- Cached boolean sort.
		do
			if internal_bool_sort = default_pointer then
				internal_bool_sort := c_mk_bool_sort (context)
			end
			Result := internal_bool_sort
		end

	real_sort: POINTER
			-- Cached real sort.
		do
			if internal_real_sort = default_pointer then
				internal_real_sort := c_mk_real_sort (context)
			end
			Result := internal_real_sort
		end

feature -- Expression factory

	int_const (a_name: STRING): SMT_EXPR
			-- Integer variable named `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			create Result.make (Current, c_mk_const (context, symbol (a_name), int_sort))
		ensure
			same_context: Result.context = Current
		end

	real_const (a_name: STRING): SMT_EXPR
			-- Real variable named `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			create Result.make (Current, c_mk_const (context, symbol (a_name), real_sort))
		ensure
			same_context: Result.context = Current
		end

	bool_const (a_name: STRING): SMT_EXPR
			-- Boolean variable named `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			create Result.make (Current, c_mk_const (context, symbol (a_name), bool_sort))
		ensure
			same_context: Result.context = Current
		end

	int_value (a_value: INTEGER): SMT_EXPR
			-- Integer literal `a_value'.
		local
			l_c: C_STRING
		do
			create l_c.make (a_value.out)
			create Result.make (Current, c_mk_numeral (context, l_c.item, int_sort))
		ensure
			same_context: Result.context = Current
		end

	real_value (a_literal: STRING): SMT_EXPR
			-- Real literal from `a_literal' (e.g. "1/2", "3.5").
		require
			literal_not_empty: not a_literal.is_empty
		local
			l_c: C_STRING
		do
			create l_c.make (a_literal)
			create Result.make (Current, c_mk_numeral (context, l_c.item, real_sort))
		ensure
			same_context: Result.context = Current
		end

	true_expr: SMT_EXPR
			-- Boolean constant true.
		do
			create Result.make (Current, c_mk_true (context))
		end

	false_expr: SMT_EXPR
			-- Boolean constant false.
		do
			create Result.make (Current, c_mk_false (context))
		end

	new_solver: SMT_SOLVER
			-- A fresh solver over this context.
		do
			create Result.make (Current)
		ensure
			same_context: Result.context = Current
		end

feature -- Disposal

	dispose_context
			-- Release the Z3 context and configuration.
		do
			if context /= default_pointer then
				c_del_context (context)
				context := default_pointer
			end
			if config /= default_pointer then
				c_del_config (config)
				config := default_pointer
			end
		end

feature {NONE} -- Symbols

	symbol (a_name: STRING): POINTER
			-- Z3 symbol for `a_name'.
		local
			l_c: C_STRING
		do
			create l_c.make (a_name)
			Result := c_mk_string_symbol (context, l_c.item)
		end

	config: POINTER
			-- Z3_config handle.

	internal_int_sort, internal_bool_sort, internal_real_sort: POINTER
			-- Sort caches.

feature {SMT_EXPR, SMT_SOLVER, SMT_MODEL} -- Z3 externals: expression building

	c_mk_add2 (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _a[2] = { (Z3_ast) $a1, (Z3_ast) $a2 };
			return Z3_mk_add ((Z3_context) $a_ctx, 2, _a);
		]"
		end

	c_mk_sub2 (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _a[2] = { (Z3_ast) $a1, (Z3_ast) $a2 };
			return Z3_mk_sub ((Z3_context) $a_ctx, 2, _a);
		]"
		end

	c_mk_mul2 (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _a[2] = { (Z3_ast) $a1, (Z3_ast) $a2 };
			return Z3_mk_mul ((Z3_context) $a_ctx, 2, _a);
		]"
		end

	c_mk_and2 (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _a[2] = { (Z3_ast) $a1, (Z3_ast) $a2 };
			return Z3_mk_and ((Z3_context) $a_ctx, 2, _a);
		]"
		end

	c_mk_or2 (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _a[2] = { (Z3_ast) $a1, (Z3_ast) $a2 };
			return Z3_mk_or ((Z3_context) $a_ctx, 2, _a);
		]"
		end

	c_mk_lt (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_lt ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_mk_le (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_le ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_mk_gt (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_gt ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_mk_ge (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_ge ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_mk_eq (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_eq ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_mk_not (a_ctx, a1: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_not ((Z3_context) $a_ctx, (Z3_ast) $a1);"
		end

	c_mk_implies (a_ctx, a1, a2: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_implies ((Z3_context) $a_ctx, (Z3_ast) $a1, (Z3_ast) $a2);"
		end

	c_ast_to_string (a_ctx, a1: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return (EIF_POINTER) Z3_ast_to_string ((Z3_context) $a_ctx, (Z3_ast) $a1);"
		end

feature {SMT_EXPR, SMT_SOLVER, SMT_MODEL} -- Z3 externals: solver & model

	c_mk_solver (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_solver ((Z3_context) $a_ctx);"
		end

	c_solver_inc_ref (a_ctx, a_s: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_inc_ref ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_dec_ref (a_ctx, a_s: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_dec_ref ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_assert (a_ctx, a_s, a_f: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_assert ((Z3_context) $a_ctx, (Z3_solver) $a_s, (Z3_ast) $a_f);"
		end

	c_solver_check (a_ctx, a_s: POINTER): INTEGER
		external "C inline use %"z3.h%""
		alias "return (EIF_INTEGER) Z3_solver_check ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_push (a_ctx, a_s: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_push ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_pop (a_ctx, a_s: POINTER; a_n: INTEGER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_pop ((Z3_context) $a_ctx, (Z3_solver) $a_s, (unsigned) $a_n);"
		end

	c_solver_reset (a_ctx, a_s: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_solver_reset ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_get_model (a_ctx, a_s: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_solver_get_model ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_solver_to_string (a_ctx, a_s: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return (EIF_POINTER) Z3_solver_to_string ((Z3_context) $a_ctx, (Z3_solver) $a_s);"
		end

	c_model_inc_ref (a_ctx, a_m: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_model_inc_ref ((Z3_context) $a_ctx, (Z3_model) $a_m);"
		end

	c_model_dec_ref (a_ctx, a_m: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_model_dec_ref ((Z3_context) $a_ctx, (Z3_model) $a_m);"
		end

	c_model_eval (a_ctx, a_m, a_expr: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "[
			Z3_ast _v;
			if (Z3_model_eval ((Z3_context) $a_ctx, (Z3_model) $a_m, (Z3_ast) $a_expr, true, &_v))
				return _v;
			return (EIF_POINTER) 0;
		]"
		end

	c_get_numeral_string (a_ctx, a1: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return (EIF_POINTER) Z3_get_numeral_string ((Z3_context) $a_ctx, (Z3_ast) $a1);"
		end

	c_model_to_string (a_ctx, a_m: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return (EIF_POINTER) Z3_model_to_string ((Z3_context) $a_ctx, (Z3_model) $a_m);"
		end

	c_get_bool_value (a_ctx, a1: POINTER): INTEGER
		external "C inline use %"z3.h%""
		alias "return (EIF_INTEGER) Z3_get_bool_value ((Z3_context) $a_ctx, (Z3_ast) $a1);"
		end

feature {NONE} -- Z3 externals: lifecycle

	c_mk_config: POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_config ();"
		end

	c_del_config (a_cfg: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_del_config ((Z3_config) $a_cfg);"
		end

	c_mk_context (a_cfg: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_context ((Z3_config) $a_cfg);"
		end

	c_del_context (a_ctx: POINTER)
		external "C inline use %"z3.h%""
		alias "Z3_del_context ((Z3_context) $a_ctx);"
		end

	c_mk_string_symbol (a_ctx, a_name: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return (EIF_POINTER) Z3_mk_string_symbol ((Z3_context) $a_ctx, (Z3_string) $a_name);"
		end

	c_mk_const (a_ctx, a_sym, a_sort: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_const ((Z3_context) $a_ctx, (Z3_symbol) $a_sym, (Z3_sort) $a_sort);"
		end

	c_mk_int_sort (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_int_sort ((Z3_context) $a_ctx);"
		end

	c_mk_bool_sort (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_bool_sort ((Z3_context) $a_ctx);"
		end

	c_mk_real_sort (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_real_sort ((Z3_context) $a_ctx);"
		end

	c_mk_numeral (a_ctx, a_str, a_sort: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_numeral ((Z3_context) $a_ctx, (Z3_string) $a_str, (Z3_sort) $a_sort);"
		end

	c_mk_true (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_true ((Z3_context) $a_ctx);"
		end

	c_mk_false (a_ctx: POINTER): POINTER
		external "C inline use %"z3.h%""
		alias "return Z3_mk_false ((Z3_context) $a_ctx);"
		end

invariant
	config_or_disposed: (config /= default_pointer) or (context = default_pointer)

end
