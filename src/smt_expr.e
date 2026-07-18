note
	description: "[
		A logical expression: a Z3 AST node plus the context that owns it.
		Fluent builders return new SMT_EXPR nodes, so formulas read like the
		mathematics they denote:  x.at_least (zero).implies (x.plus (one).greater (zero)).
	]"
	author: "Larry Rix"

class
	SMT_EXPR

create
	make

feature {NONE} -- Initialization

	make (a_context: SMT_CONTEXT; a_ast: POINTER)
			-- Wrap Z3 AST `a_ast' owned by `a_context'.
		require
			ast_attached: a_ast /= default_pointer
		do
			context := a_context
			ast := a_ast
		ensure
			context_set: context = a_context
			ast_set: ast = a_ast
		end

feature -- Access

	context: SMT_CONTEXT
			-- Owning context.

	ast: POINTER
			-- Z3_ast handle.

feature -- Arithmetic

	plus (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' + `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_add2 (context.context, ast, a_other.ast))
		end

	minus (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' - `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_sub2 (context.context, ast, a_other.ast))
		end

	times (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' * `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_mul2 (context.context, ast, a_other.ast))
		end

	modulo (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' mod `a_other' (integer modulo; Z3 mod is non-negative).
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_mod (context.context, ast, a_other.ast))
		end

	divided_by (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' div `a_other' (integer division).
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_div (context.context, ast, a_other.ast))
		end

	opposite: SMT_EXPR
			-- Unary minus: -`Current'.
		do
			create Result.make (context, context.c_mk_unary_minus (context.context, ast))
		end

feature -- Comparison (yield boolean expressions)

	less (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' < `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_lt (context.context, ast, a_other.ast))
		end

	at_most (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' <= `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_le (context.context, ast, a_other.ast))
		end

	greater (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' > `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_gt (context.context, ast, a_other.ast))
		end

	at_least (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' >= `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_ge (context.context, ast, a_other.ast))
		end

	is_equal_to (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' = `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_eq (context.context, ast, a_other.ast))
		end

feature -- Boolean connectives

	conjoined (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' and `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_and2 (context.context, ast, a_other.ast))
		end

	disjoined (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' or `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_or2 (context.context, ast, a_other.ast))
		end

	entails (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' implies `a_other' (logical implication; `implies' is an
			-- Eiffel keyword, so the feature is named `entails').
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_implies (context.context, ast, a_other.ast))
		end

	negated: SMT_EXPR
			-- not `Current'.
		do
			create Result.make (context, context.c_mk_not (context.context, ast))
		end

	xored (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' xor `a_other'.
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_xor (context.context, ast, a_other.ast))
		end

	iff (a_other: SMT_EXPR): SMT_EXPR
			-- `Current' <-> `a_other' (boolean equivalence).
		require
			same_context: a_other.context = context
		do
			create Result.make (context, context.c_mk_iff (context.context, ast, a_other.ast))
		end

	when_true_else (a_then, a_else: SMT_EXPR): SMT_EXPR
			-- if `Current' then `a_then' else `a_else' (Current must be boolean).
		require
			then_same_context: a_then.context = context
			else_same_context: a_else.context = context
		do
			create Result.make (context, context.c_mk_ite (context.context, ast, a_then.ast, a_else.ast))
		end

feature -- Output

	to_string: STRING
			-- SMT-LIB rendering of this expression.
		local
			l_ptr: POINTER
		do
			l_ptr := context.c_ast_to_string (context.context, ast)
			if l_ptr /= default_pointer then
				create Result.make_from_c (l_ptr)
			else
				create Result.make_empty
			end
		end

invariant
	ast_attached: ast /= default_pointer
	context_attached: context /= Void

end
