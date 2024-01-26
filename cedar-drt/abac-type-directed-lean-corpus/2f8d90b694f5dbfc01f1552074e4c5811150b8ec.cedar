forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (({"": ip("2088.208.208.208")}[""]) == ({"": ip("208.208.208.208")}[""]))) && (({"": ip("100.105.0.208/0")}[""]) == (ip("0.0.0.0")))) && false
};
