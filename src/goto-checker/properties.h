/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#ifndef CPROVER_GOTO_CHECKER_PROPERTIES_H
#define CPROVER_GOTO_CHECKER_PROPERTIES_H

#include <unordered_map>

#include <goto-programs/goto_model.h>

class json_objectt;
class xmlt;

/// The result status of a property
enum class property_resultt
{
  /// The property was not reached (also used for initialization)
  NOT_REACHED,
  /// The status of the property is unknown
  UNKNOWN,
  /// The property was proven to be unreachable
  NOT_REACHABLE,
  /// The property was not violated
  PASS,
  /// The property was violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

std::string as_string(property_resultt result);

/// The result of goto checking and verifying
enum class resultt
{
  /// No property was violated, neither was there an error
  UNKNOWN,
  /// No properties were violated
  PASS,
  /// Some properties were violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

std::string as_string(resultt result);

struct property_infot
{
  /// A pointer to the corresponding goto instruction
  goto_programt::const_targett location;

  /// A description (usually derived from the assertion's comment)
  std::string description;

  /// The status of the property
  property_resultt result;
};

/// A map of property IDs to property infos
typedef std::unordered_map<irep_idt, property_infot> propertiest;

/// Returns the properties in the goto model
propertiest initialize_properties(const goto_modelt &);

property_resultt &operator|=(property_resultt &, property_resultt const &);
property_resultt &operator&=(property_resultt &, property_resultt const &);

resultt determine_result(const propertiest &properties);
bool has_properties_to_check(const propertiest &properties);
std::size_t count_properties(const propertiest &, property_resultt);

propertiest &operator|=(
  propertiest &properties, const propertiest &updated_properties);

int result_to_exit_code(resultt result);

#endif // CPROVER_GOTO_CHECKER_PROPERTIES_H
