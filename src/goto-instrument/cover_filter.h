/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H

#include <regex>

#include <util/message.h>
#include <util/invariant.h>

#include <goto-programs/goto_model.h>


/// Base class for filtering functions
class function_filter_baset:public messaget
{
public:
  explicit function_filter_baset(message_handlert &message_handler):
    messaget(message_handler)
  {}

  virtual ~function_filter_baset() {}

  /// Returns true if the function passes the filter criteria
  virtual bool operator()(
    const irep_idt &identifier,
    const goto_functionst::goto_functiont &goto_function) const
  {
    UNREACHABLE;
  }

  virtual void report_anomalies() const
  {
    // do nothing by default
  }
};

/// Base class for filtering goals
class goal_filter_baset:public messaget
{
public:
  explicit goal_filter_baset(message_handlert &message_handler):
    messaget(message_handler)
  {}

  virtual ~goal_filter_baset() {}

  /// Returns true if the goal passes the filter criteria
  virtual bool operator()(const source_locationt &) const
  {
    UNREACHABLE;
  }

  virtual void report_anomalies() const
  {
    // do nothing by default
  }
};

class function_filterst
{
public:
  void add(const function_filter_baset &filter)
  {
    filters.push_back(filter);
  }

  bool operator()(
    const irep_idt &identifier,
    const goto_functionst::goto_functiont &goto_function) const
  {
    for(const auto &filter : filters)
      if(!filter(identifier, goto_function))
        return false;
    
    return true;
  }

  void report_anomalies() const
  {
    for(const auto &filter : filters)
      filter.report_anomalies();
  }

private:
  std::vector<function_filter_baset> filters;
};

class goal_filterst
{
public:
  void add(const goal_filter_baset &filter)
  {
    filters.push_back(filter);
  }

  bool operator()(
    const source_locationt &source_location) const
  {
    for(const auto &filter : filters)
      if(!filter(source_location))
        return false;
    
    return true;
  }

  void report_anomalies() const
  {
    for(const auto &filter : filters)
      filter.report_anomalies();
  }
  
private:
  std::vector<goal_filter_baset> filters;
};

  
/// Filters out CPROVER internal functions
class internal_functions_filtert:public function_filter_baset
{
public:
  explicit internal_functions_filtert(message_handlert &message_handler):
    function_filter_baset(message_handler)
  {}

  bool operator()(
    const irep_idt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;
};

/// Filters functions that match the provided pattern
class include_pattern_filtert:public function_filter_baset
{
public:
  explicit include_pattern_filtert(
    message_handlert &message_handler,
    const std::string &cover_include_pattern):
    function_filter_baset(message_handler),
    regex_matcher(cover_include_pattern)
  {}

  bool operator()(
    const irep_idt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;

private:
  std::regex regex_matcher;
};

/// Filters out existing goals
class existing_goals_filtert:public goal_filter_baset
{
public:
  existing_goals_filtert(
    message_handlert &message_handler,
    const std::string &filename,
    const irep_idt &mode);
  
  bool operator()(const source_locationt &) const override;
  void report_anomalies() const override;

private:
  mutable std::map<source_locationt, bool> goals;
};

/// Filters out trivial functions
class trivial_functions_filtert:public function_filter_baset
{
public:
  explicit trivial_functions_filtert(message_handlert &message_handler):
    function_filter_baset(message_handler)
  {}

  bool operator()(
    const irep_idt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;
};

/// Filters out goals with source locations considered internal
class internal_goals_filtert:public goal_filter_baset
{
public:
  internal_goals_filtert(message_handlert &message_handler):
    goal_filter_baset(message_handler)
  {}
  
  bool operator()(const source_locationt &) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H
