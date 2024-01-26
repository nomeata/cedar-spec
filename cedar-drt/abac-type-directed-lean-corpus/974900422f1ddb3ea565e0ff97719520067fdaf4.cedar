permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (x::"" in x::"")) && (x::"#" in principal)
};
