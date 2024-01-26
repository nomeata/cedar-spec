permit(
  principal,
  action,
  resource
) when {
  ((true && [!((!(Ah000::"" < principal)) < principal)]) && principal) && principal
};
