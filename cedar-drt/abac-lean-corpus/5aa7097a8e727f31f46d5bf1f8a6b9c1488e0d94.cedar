@Ahhh("")
@r("")
permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  true && [false, !false, a::"jjj" in (!a::"jjj")]
};
