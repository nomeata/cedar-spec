permit(
  principal is a in a::"\t",
  action in [Action::"action"],
  resource is a in a::"\t"
) when {
  (true && (resource in resource)) && ([] == [[]])
};
