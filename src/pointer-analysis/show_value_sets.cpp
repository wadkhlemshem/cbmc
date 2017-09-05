/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#include "show_value_sets.h"

#include <util/xml.h>
#include <util/invariant.h>

#include "value_set_analysis.h"

void show_value_sets(
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis)
{
  messaget message(ui_message_handler);

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(goto_functions, value_set_analysis, xml);
      message.status() << messaget::preformatted_output
                       << xml << messaget::eom;
    }
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(goto_functions, message.status());
    message.status() << messaget::eom;
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      // TODO: implement JSON support
      message.error() << "JSON output not available" << messaget::eom;
    }
    break;
  }
}

void show_value_sets(
  ui_message_handlert &ui_message_handler,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis)
{
  messaget message(ui_message_handler);

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(goto_program, value_set_analysis, xml);
      message.status() << messaget::preformatted_output
                       << xml << messaget::eom;
    }
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(goto_program, message.status());
    message.status() << messaget::eom;
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      // TODO: implement JSON support
      message.error() << "JSON output not available" << messaget::eom;
    }
    break;
  }
}
