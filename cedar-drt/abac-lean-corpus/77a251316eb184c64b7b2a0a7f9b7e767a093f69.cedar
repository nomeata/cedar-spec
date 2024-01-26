permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && (if a::"" then ((!a::"") == a::"") else a::"")
};
