forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (resource in resource)) && ("" == "")) && (a::"" in [resource, principal, principal])
};
