permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (!(Action::"action"[""]))) && false
};
