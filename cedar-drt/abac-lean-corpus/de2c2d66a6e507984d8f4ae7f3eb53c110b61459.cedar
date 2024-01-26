permit(
  principal == AhgAOVh::a::"",
  action in [AhgAOVh::Action::"action"],
  resource is AhgAOVh::a
) when {
  (true && (if false then action else action)) && principal
};
