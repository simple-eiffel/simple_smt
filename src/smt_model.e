note
	description: "A satisfying assignment produced by Z3; evaluate expressions in it"
	author: "Larry Rix"

class
	SMT_MODEL

create
	make

feature {NONE} -- Initialization

	make (a_context: SMT_CONTEXT; a_model: POINTER)
			-- Wrap Z3_model `a_model' (ref-counted for our lifetime).
		require
			model_attached: a_model /= default_pointer
		do
			context := a_context
			model := a_model
			context.c_model_inc_ref (context.context, model)
		ensure
			context_set: context = a_context
			model_set: model = a_model
		end

feature -- Access

	context: SMT_CONTEXT
			-- Owning context.

	model: POINTER
			-- Z3_model handle.

	value_of (a_expr: SMT_EXPR): STRING
			-- Value of `a_expr' in this model as text ("" if it cannot be evaluated).
		require
			same_context: a_expr.context = context
		local
			l_val, l_str: POINTER
			l_bool: INTEGER
		do
			create Result.make_empty
			l_val := context.c_model_eval (context.context, model, a_expr.ast)
			if l_val /= default_pointer then
					-- Try boolean first (Z3_L_TRUE=1, Z3_L_FALSE=-1, Z3_L_UNDEF=0).
				l_bool := context.c_get_bool_value (context.context, l_val)
				if l_bool = 1 then
					Result := "true"
				elseif l_bool = -1 then
					Result := "false"
				else
					l_str := context.c_get_numeral_string (context.context, l_val)
					if l_str /= default_pointer then
						create Result.make_from_c (l_str)
					end
				end
			end
		ensure
			result_attached: Result /= Void
		end

	to_string_representation: STRING
			-- Full textual rendering of the model (all variable assignments).
		local
			l_ptr: POINTER
		do
			l_ptr := context.c_model_to_string (context.context, model)
			if l_ptr /= default_pointer then
				create Result.make_from_c (l_ptr)
			else
				create Result.make_empty
			end
		ensure
			result_attached: Result /= Void
		end

feature -- Disposal

	dispose_model
			-- Release the model.
		do
			if model /= default_pointer then
				context.c_model_dec_ref (context.context, model)
				model := default_pointer
			end
		end

invariant
	context_attached: context /= Void

end
