@Afhhh("jjjj")
permit(
  principal == a::"",
  action,
  resource
) when {
  (true && [Action::"action", principal]) && false
};
