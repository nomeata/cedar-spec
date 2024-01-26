permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && (if a::"\0\0" then true else a::"")
};
