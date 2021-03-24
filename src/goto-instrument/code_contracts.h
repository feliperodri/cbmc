/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

#include <set>
#include <string>
#include <unordered_set>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <util/c_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>

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
    const irep_idt &mode);

  const namespacet &get_namespace() const;

  // for "helper" classes to update symbol table.
  symbol_tablet &get_symbol_table();
  goto_functionst &get_goto_functions();

protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  unsigned temporary_counter;
  messaget &log;

  std::unordered_set<irep_idt> summarized;

  /// \brief Enforce contract of a single function
  bool enforce_contract(const std::string &);

  /// Create code corresponding to assertion/assumption
  void convert_to_goto(const codet &code, const irep_idt &mode, goto_programt &target);

  /// Insert assertion statements into the goto program to ensure that
  /// assigned memory is within the assignable memory frame.
  bool add_pointer_checks(const std::string &);

  /// Check if there are any malloc statements which may be repeated because of
  /// a goto statement that jumps back.
  bool check_for_looped_mallocs(const goto_programt &);

  /// Inserts an assertion statement into program before the assignment
  /// instruction_it, to ensure that the left-hand-side of the assignment
  /// aliases some expression in original_references, unless it is contained
  /// in freely_assignable_exprs.
  void instrument_assign_statement(
    goto_programt::instructionst::iterator &instruction_it,
    goto_programt &program,
    exprt &assigns,
    std::set<irep_idt> &freely_assignable_symbols,
    assigns_clauset &assigns_clause);

  /// Inserts an assertion statement into program before the function call at
  /// ins_it, to ensure that any memory which may be written by the call is
  /// aliased by some expression in assigns_references,unless it is contained
  /// in freely_assignable_exprs.
  void instrument_call_statement(
    goto_programt::instructionst::iterator &ins_it,
    goto_programt &program,
    exprt &assigns,
    const irep_idt &function_id,
    std::set<irep_idt> &freely_assignable_symbols,
    assigns_clauset &assigns_clause);

  /// Creates a local variable declaration for each expression in operands,
  /// and stores them in created_declarations. Then creates assignment
  /// statements to capture the memory addresses of each expression
  /// in the assigns clause within the associated local variable,
  /// populating a vector created_references of these local variables.
  void populate_assigns_reference(
    std::vector<exprt> operands,
    const symbolt &function_symbol,
    const irep_idt &function_id,
    goto_programt &created_declarations,
    std::vector<exprt> &created_references);

  /// Creates a boolean expression which is true when there exists an expression
  /// in aliasable_references with the same pointer object and pointer offset as
  /// the address of lhs.
  exprt create_alias_expression(
    const exprt &lhs,
    std::vector<exprt> &aliasable_references);

  void apply_loop_contract(goto_functionst::goto_functiont &goto_function);

  /// \brief Does the named function have a contract?
  bool has_contract(const irep_idt);

  bool apply_function_contract(
    const irep_idt &function_id,
    goto_programt &goto_program,
    goto_programt::targett target);

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

/// \brief A base class for assigns clause targets
class assigns_clause_targett
{
public:
  enum target_type
  {
    Scalar,
    Struct,
    Array
  };

  assigns_clause_targett(
    target_type type,
    const exprt object_ptr,
    const code_contractst &contract,
    messaget &log_parameter)
    : target_type(type),
      pointer_object(object_ptr),
      contract(contract),
      init_block(),
      log(log_parameter)
  {
    INVARIANT(
      pointer_object.type().id() == ID_pointer,
      "Assigns clause targets should be stored as pointer expressions.");
  }

  virtual ~assigns_clause_targett()
  {
  }

  virtual std::vector<symbol_exprt> temporary_declarations() const = 0;
  virtual exprt alias_expression(const exprt &lhs) = 0;
  virtual exprt
  compatible_expression(const assigns_clause_targett &called_target) = 0;
  virtual goto_programt havoc_code(source_locationt location) const = 0;

  const exprt &get_direct_pointer() const
  {
    return pointer_object;
  }

  goto_programt &get_init_block()
  {
    return init_block;
  }

  static exprt pointer_for(const exprt &exp)
  {
    return address_of_exprt(exp);
  }

  const target_type target_type;

protected:
  const exprt pointer_object;
  const code_contractst &contract;
  goto_programt init_block;
  messaget &log;
};

class assigns_clause_scalar_targett : public assigns_clause_targett
{
public:
  assigns_clause_scalar_targett(
    const exprt &object_ptr,
    code_contractst &contract,
    messaget &log_parameter,
    const irep_idt &function_id);

  std::vector<symbol_exprt> temporary_declarations() const;
  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clause_targett &called_target);
  goto_programt havoc_code(source_locationt location) const;

protected:
  symbol_exprt local_standin_variable;
};

class assigns_clause_struct_targett : public assigns_clause_targett
{
public:
  assigns_clause_struct_targett(
    const exprt &object_ptr,
    code_contractst &contract,
    messaget &log_parameter,
    const irep_idt &function_id);

  std::vector<symbol_exprt> temporary_declarations() const;
  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clause_targett &called_target);
  goto_programt havoc_code(source_locationt location) const;

protected:
  symbol_exprt main_struct_standin;
  std::vector<symbol_exprt> local_standin_variables;
};

class assigns_clause_array_targett : public assigns_clause_targett
{
public:
  assigns_clause_array_targett(
    const exprt &object_ptr,
    code_contractst &contract,
    messaget &log_parameter,
    const irep_idt &function_id);

  std::vector<symbol_exprt> temporary_declarations() const;
  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clause_targett &called_target);
  goto_programt havoc_code(source_locationt location) const;

protected:
  mp_integer lower_bound;
  mp_integer upper_bound;

  exprt lower_offset_object;
  exprt upper_offset_object;

  symbol_exprt array_standin_variable;
  symbol_exprt lower_offset_variable;
  symbol_exprt upper_offset_variable;
};

class assigns_clauset
{
public:
  assigns_clauset(
    const exprt &assigns,
    code_contractst &contract,
    const irep_idt function_id,
    messaget log_parameter);
  ~assigns_clauset();

  assigns_clause_targett *add_target(exprt current_operation);
  assigns_clause_targett *add_pointer_target(exprt current_operation);
  goto_programt init_block(source_locationt location);
  goto_programt &temporary_declarations(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  goto_programt dead_stmts(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  goto_programt havoc_code(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  exprt alias_expression(const exprt &lhs);

  exprt compatible_expression(const assigns_clauset &called_assigns);

protected:
  const exprt &assigns_expr;

  std::vector<assigns_clause_targett *> targets;
  goto_programt standin_declarations;

  code_contractst &parent;
  const irep_idt function_id;
  messaget log;
};

/********************************************
 * is_fresh allocation and checking
 *
 *   - for contract enforcement, creates an infinite map that records the allocated elements in preconditions
 *     and a function for each type used in a contract that returns an object or array of that type.  For
 *     postcondition, it ensures that an object is 'fresh' (e.g., not previously created)
 *      Declarations:
 *        static uint8_t __<fn_name>_memory_map[__CPROVER_constant_infinity_uint];
 *        For each referenced type:
 *          static bool __<fn_name>_<type>_requires_is_fresh(<type> *elem, size_t size);
 *          static bool __<fn_name>_<type>_ensures_is_fresh(<type> *elem, size_t size);
 *
 *   - for contract use, we need to create dual declarations.  For the precondition, we need to check that
 *     all objects mapped to "fresh" objects are distinct.  For the postcondition, if an object is "fresh",
 *     we need to create a new object to represent it.
 *
 *      Declarations (per call):
 *        static uint8_t <fn_name>_memory_map[__CPROVER_constant_infinity_uint];
 *        For each referenced type:
 *          static bool __call_<fn_name>_<type>_requires_is_fresh(<type> *elem, size_t size);
 *          static bool __call_<fn_name>_<type>_ensures_is_fresh(<type> *elem, size_t size);
 *
 *     Note that for a given context, we may have multiple calls to the same function, so we have to be sure to
 *     create unique identifiers for the declarations.
 *
 *   Need symbol table to create new symbols and functions.
 *   Need set of types to determine which functions to construct.
 *
 *   Procedure:
 *     - Visit both the requires/asserts expressions to determine the set of called functions and their types.
 *     - Generate declarations for is_fresh and memory_maps and record the names for...
 *     - Doing replacements for code.
 *
 *******************************************/
class is_fresh_baset {
public:
  is_fresh_baset(code_contractst &_parent,
                 messaget _log,
                 const irep_idt _fun_id) : parent(_parent), log(_log), fun_id(_fun_id)  {};

  void update_requires(goto_programt &requires);
  void update_ensures(goto_programt &ensures);

  virtual void create_declarations() = 0;

protected:
  void add_declarations(const std::string &decl_string);
  void update_fn_call(goto_programt::targett &target, const std::string &name, bool add_address_of);

  virtual void create_requires_fn_call(goto_programt::targett &target) = 0;
  virtual void create_ensures_fn_call(goto_programt::targett &target) = 0;

  code_contractst &parent;
  messaget log;
  irep_idt fun_id;

  // written by the child classes.
  std::string memmap_name;
  std::string requires_fn_name;
  std::string ensures_fn_name;

};


class is_fresh_enforcet : public is_fresh_baset {
public:
  is_fresh_enforcet(code_contractst &_parent,
                    messaget _log,
                    const irep_idt _fun_id);

    virtual void create_declarations();

protected:
    virtual void create_requires_fn_call(goto_programt::targett &target);
    virtual void create_ensures_fn_call(goto_programt::targett &target);

};

class is_fresh_replacet : public is_fresh_baset {
public:
  is_fresh_replacet(code_contractst &_parent,
                    messaget _log,
                    const irep_idt _fun_id);

  virtual void create_declarations();

protected:
    virtual void create_requires_fn_call(goto_programt::targett &target);
    virtual void create_ensures_fn_call(goto_programt::targett &target);

};


#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
