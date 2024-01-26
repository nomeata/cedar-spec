permit(
  principal == Ahhhh::a::"",
  action in [Ahhhh::Action::"action"],
  resource == Ahhhh::a::""
) when {
  (true && A::"\0") && (A::"" == principal)
};
