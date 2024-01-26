forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (action is a)) && ((if (resource is a) then principal else a::"7") is a)) && false
};
