@b("")
permit(
  principal == a::"\0666",
  action == Action::"action",
  resource is a in a::"\0666"
) when {
  false
};
