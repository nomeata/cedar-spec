forbid(
  principal is a in a::"\"\0\062",
  action in [Action::"66"],
  resource is a in a::"\"\0\062"
) when {
  false && (J::"" in action)
};
