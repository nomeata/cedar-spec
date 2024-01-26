@r("\033")
permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true
};
