permit(
  principal == K::a::"",
  action,
  resource
) when {
  (true && principal) && principal
};
