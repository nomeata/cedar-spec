permit(
  principal == B::a::".$\0\0",
  action in [B::Action::"action"],
  resource is B::a in B::a::".$\0\0"
) when {
  true && (action has "")
};
