/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

#include <iostream>
#include <set>
#include <string>
#include <unordered_set>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <util/c_types.h>
#include <util/namespace.h>
#include <util/message.h>

class messaget;
class assigns_clauset;

class code_contractst
{
public:
  code_contractst(goto_modelt &goto_model, messaget &log)
    : ns(goto_model.symbol_table),
      symbol_table(goto_model.symbol_table),
      goto_functions(goto_model.goto_functions),
      temporary_counter(0),
      log(log)
  {
  }

  /// \brief Replace all calls to each function in the list with that function's
  ///        contract
  ///
  /// Use this function when proving code that calls into an expensive function,
  /// `F`. You can write a contract for F using __CPROVER_requires and
  /// __CPROVER_ensures, and then use this function to replace all calls to `F`
  /// with an assertion that the `requires` clause holds followed by an
  /// assumption that the `ensures` clause holds. In order to ensure that `F`
  /// actually abides by its `ensures` and `requires` clauses, you should
  /// separately call `code_constractst::enforce_contracts()` on `F` and verify
  /// it using `cbmc --function F`.
  ///
  /// \return `true` on failure, `false` otherwise
  bool replace_calls(const std::set<std::string> &);

  /// \brief Turn requires & ensures into assumptions and assertions for each of
  ///        the named functions
  ///
  /// Use this function to prove the correctness of a function F independently
  /// of its calling context. If you have proved that F is correct, then you can
  /// soundly replace all calls to F with F's contract using the
  /// code_contractst::replace_calls() function; this means that symbolic
  /// execution does not need to explore F every time it is called, increasing
  /// scalability.
  ///
  /// Implementation: mangle the name of each function F into a new name,
  /// `__CPROVER_contracts_original_F` (`CF` for short). Then mint a new
  /// function called `F` that assumes `CF`'s `requires` clause, calls `CF`, and
  /// then asserts `CF`'s `ensures` clause.
  ///
  /// \return `true` on failure, `false` otherwise
  bool enforce_contracts(const std::set<std::string> &);

  /// \brief Call enforce_contracts() on all functions that have a contract
  /// \return `true` on failure, `false` otherwise
  bool enforce_contracts();

  /// \brief Call replace_calls() on all calls to any function that has a
  ///        contract
  /// \return `true` on failure, `false` otherwise
  bool replace_calls();

  const symbolt &new_tmp_symbol(
          const typet &type,
          const source_locationt &source_location,
          const irep_idt &function_id,
          const irep_idt &mode) const;

  const namespacet &get_namespace() const;

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  unsigned temporary_counter;
  messaget &log;

  std::unordered_set<irep_idt> summarized;

  /// \brief Enforce contract of a single function
  bool enforce_contract(const std::string &);


  /// Insert assertion statements into the goto program to ensure that
  /// assigned memory is within the assignable memory frame.
  bool
  add_pointer_checks(const std::string &);

  /// Check if there are any malloc statements which may be repeated because of
  /// a goto statement that jumps back.
  bool
  check_for_looped_mallocs(const goto_programt &);

  /// Inserts an assertion statement into program before the assignment ins_it, to
  /// ensure that the left-hand-side of the assignment aliases some expression in
  /// original_references, unless it is contained in freely_assignable_exprs.
  void
  instrument_assn_statement(
    const std::string &func_name,
    goto_programt::instructionst::iterator& ins_it,
    goto_programt& program,
    exprt& assigns,
    std::set<dstringt>& freely_assignable_symbols,
    assigns_clauset &assigns_clause);


  /// Inserts an assertion statement into program before the function call at
  /// ins_it, to ensure that any memory which may be written by the call is
  /// aliased by some expression in assigns_references,unless it is contained
  /// in freely_assignable_exprs.
  void
  instrument_call_statement(
    goto_programt::instructionst::iterator& ins_it,
    goto_programt& program,
    exprt& assigns,
    const irep_idt &func_id,
    std::set<dstringt>& freely_assignable_symbols,
    assigns_clauset &assigns_clause);

  /// Creates a local variable declaration for each expression in the assigns
  /// clause (of the function given by f_sym), and stores them in created_decls.
  /// Then creates assignment statements to capture the memory addresses of each
  /// expression in the assigns clause within the associated local variable,
  /// populating a vector created_references of these local variables.
  void
  populate_assigns_references(
    const symbolt &f_sym,
    const irep_idt& func_id,
    goto_programt& created_decls,
    std::vector<exprt>& created_references);


  /// Creates a local variable declaration for each expression in operands,
  /// and stores them in created_decls. Then creates assignment statements to
  /// capture the memory addresses of each expression in the assigns clause
  /// within the associated local variable, populating a vector
  /// created_references of these local variables.
  void
  populate_assigns_reference(
    std::vector<exprt> operands,
    const symbolt &f_sym,
    const irep_idt &func_id,
    goto_programt &created_decls,
    std::vector<exprt>& created_references);

  /// Creates a boolean expression which is true when there exists an expression
  /// in aliasable_references with the same pointer object and pointer offset as
  /// the address of lhs.
  exprt
  create_alias_expression(
    const exprt &lhs,
    std::vector<exprt> &aliasable_references);

  void code_contracts(goto_functionst::goto_functiont &goto_function);

  /// \brief Does the named function have a contract?
  bool has_contract(const irep_idt);

  bool
  apply_contract(const irep_idt &func_id, goto_programt &goto_program, goto_programt::targett target);

  void
  add_contract_check(const irep_idt &, const irep_idt &, goto_programt &dest);
};

#define FLAG_REPLACE_CALL "replace-call-with-contract"
#define HELP_REPLACE_CALL                                                      \
  " --replace-call-with-contract <fun>\n"                                      \
  "                              replace calls to fun with fun's contract\n"

#define FLAG_REPLACE_ALL_CALLS "replace-all-calls-with-contracts"
#define HELP_REPLACE_ALL_CALLS                                                 \
  " --replace-all-calls-with-contracts\n"                                      \
  "                              as above for all functions with a contract\n"

#define FLAG_ENFORCE_CONTRACT "enforce-contract"
#define HELP_ENFORCE_CONTRACT                                                  \
  " --enforce-contract <fun>     wrap fun with an assertion of its contract\n"

#define FLAG_ENFORCE_ALL_CONTRACTS "enforce-all-contracts"
#define HELP_ENFORCE_ALL_CONTRACTS                                             \
  " --enforce-all-contracts      as above for all functions with a contract\n"

/*********************************************
 *  Assigns Clause Target - Base
 ********************************************/
//#define pointer_for(exp)  (exp.id() == ID_dereference ? to_dereference_expr(exp).pointer() : exprt(ID_address_of, pointer_type(exp.type()), {exp}))
//#define pointer_for(exp)  (exp.id() == ID_dereference ? to_dereference_expr(exp).pointer() : (exp))
class assigns_clause_targett
{

public:
    enum TargetType {Scalar, Struct, Array};

    assigns_clause_targett(TargetType type, const exprt obj_ptr, const code_contractst &contr, messaget &log_param) :
            tgt_type(type), obj_pointer(obj_ptr), contract(contr), init_block(), log(log_param)
    {
      INVARIANT(
        obj_pointer.type().id() == ID_pointer,
        "Assigns clause targets should be stored as pointer expressions.");
    }

    virtual ~assigns_clause_targett() {}

    virtual std::vector<symbol_exprt> temporary_declarations() const = 0;
    virtual exprt alias_expression(const exprt &lhs) = 0;
    virtual exprt compatible_expression(const assigns_clause_targett &called_target) = 0;
    virtual goto_programt havoc_code(source_locationt loc) const = 0;

    const exprt &get_direct_pointer() const
    {
      return obj_pointer;
    }

    goto_programt &get_init_block()
    {
        return init_block;
    }

    static const exprt pointer_for(const exprt &exp)
    {
      const exprt &left_ptr = exprt(ID_address_of, pointer_type(exp.type()), {exp});
        if(exp.id() == ID_dereference)
        {
            return to_dereference_expr(exp).pointer();
        }

      return left_ptr;
    }

    const TargetType tgt_type;

protected:
    const exprt obj_pointer;
    const code_contractst contract;
    goto_programt init_block;
    messaget &log;
};

/*********************************************
 *  Assigns Clause Target - Scalar
 ********************************************/
class assigns_clause_scalar_targett : public assigns_clause_targett
{
public:
    assigns_clause_scalar_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id);

    std::vector<symbol_exprt> temporary_declarations() const;
    exprt alias_expression(const exprt &lhs);
    exprt compatible_expression(const assigns_clause_targett &called_target);
    goto_programt havoc_code(source_locationt loc) const;

protected:
  symbol_exprt local_standin_var;
};

/*********************************************
 *  Assigns Clause Target - Struct
 ********************************************/
class assigns_clause_struct_targett : public assigns_clause_targett
{
public:
    assigns_clause_struct_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id);

    std::vector<symbol_exprt> temporary_declarations() const;
    exprt alias_expression(const exprt &lhs);
    exprt compatible_expression(const assigns_clause_targett &called_target);
    goto_programt havoc_code(source_locationt loc) const;

protected:
    symbol_exprt main_struct_standin;
    std::vector<symbol_exprt> local_standin_vars;
};

/*********************************************
 *  Assigns Clause Target - Array
 ********************************************/
class assigns_clause_array_targett : public assigns_clause_targett
{
public:
    assigns_clause_array_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id);

    std::vector<symbol_exprt> temporary_declarations() const;
    exprt alias_expression(const exprt &lhs);
    exprt compatible_expression(const assigns_clause_targett &called_target);
    goto_programt havoc_code(source_locationt loc) const;

protected:
    int lower_bound;
    int upper_bound;

    exprt lower_offset_obj;
    exprt upper_offset_obj;

    symbol_exprt arr_standin_var;
    symbol_exprt lower_offset_var;
    symbol_exprt upper_offset_var;
};

/*********************************************
 *  Assigns Clause
 ********************************************/
class assigns_clauset
{
public:
    assigns_clauset(const exprt &assigns, code_contractst &contract,
                    const irep_idt f_id, messaget log_param);
    ~assigns_clauset();

    assigns_clause_targett* add_target(exprt curr_op);
    assigns_clause_targett* add_pointer_target(exprt curr_op);
    goto_programt init_block(source_locationt loc);
    goto_programt &temporary_declarations(source_locationt loc, dstringt func_name, dstringt lang_mode);
    goto_programt dead_stmts(source_locationt loc, dstringt func_name, dstringt lang_mode);
    goto_programt havoc_code(source_locationt loc, dstringt func_name, dstringt lang_mode);
    exprt alias_expression(const exprt &lhs);

    exprt compatible_expression(const assigns_clauset &called_assigns);

protected:
    const exprt &assigns_expr;

    std::vector<assigns_clause_targett*> targets;
    goto_programt standin_declarations;

    code_contractst &parent;
    const irep_idt func_id;
    messaget log;
};

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
