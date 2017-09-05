/*******************************************************************\

Module: Show goto functions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_goto_functions.h"

#include <util/xml.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/xml_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>
#include <goto-programs/show_goto_functions_json.h>
#include <goto-programs/show_goto_functions_xml.h>

#include "goto_functions.h"
#include "goto_model.h"

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions)
{
  messaget message(ui_message_handler);

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::XML_UI:
  {
    show_goto_functions_xmlt xml_show_functions(ns);
    message.status() << messaget::preformatted_output;
    xml_show_functions(goto_functions, message.status());
    message.status() << messaget::eom;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    show_goto_functions_jsont json_show_functions(ns);
    message.status() << messaget::preformatted_output;
    json_show_functions(goto_functions, message.status());
    message.status() << messaget::eom;
  }
  break;

  case ui_message_handlert::uit::PLAIN:
    goto_functions.output(ns, message.status());
    message.status() << messaget::eom;
    break;
  }
}

void show_goto_functions(
  const goto_modelt &goto_model,
  ui_message_handlert &ui_message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_functions(ns, ui_message_handler, goto_model.goto_functions);
}
