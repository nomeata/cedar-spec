@A("")
@r("")
forbid(
  principal is a in a::"\t\0",
  action == Action::"action",
  resource
) when {
  true
};
