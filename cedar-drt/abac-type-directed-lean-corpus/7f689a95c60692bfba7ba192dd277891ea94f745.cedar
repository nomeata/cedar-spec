@F("")
@r("")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (Action::"action" in Action::"action")) && true
};
