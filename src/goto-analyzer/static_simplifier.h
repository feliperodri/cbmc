/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_SIMPLIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_SIMPLIFIER_H

#include <iosfwd>

#include <util/message.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

#include <analyses/ai.h>

bool static_simplifier(
  goto_modelt &,
  const ai_baset &,
  const optionst &,
  message_handlert &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_STATIC_SIMPLIFIER_H
